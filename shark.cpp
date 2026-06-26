#include <iostream>
#include <sstream> 
#include <random>
#include <string>
#include <vector>
#if defined(_WIN32) || defined(_WIN64)
#include <windows.h>
#endif

using namespace std;

#define MAX_PLY 64
#define INF 32001
#define MATE 32000
#define U8 unsigned __int8
#define S16 signed __int16
#define U16 unsigned __int16
#define S32 signed __int32
#define S64 signed __int64
#define U64 unsigned __int64
#define NAME "Shark"
#define VERSION "2025-10-13"
#define START_FEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

enum Color { WHITE, BLACK, COLOR_NB };
enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };
enum Bound { UPPER, LOWER, EXACT };

struct Position {
	bool flipped = false;
	U8 move50;
	U8 castling[4];
	U64 color[2];
	U64 pieces[6];
	U64 ep;
};

struct Move {
	U8 from = 0;
	U8 to = 0;
	U8 promo = 0;
};

const Move no_move{};

struct Stack {
	Move moves[256];
	Move moves_evaluated[256];
	S64 moves_scores[256];
	Move move;
	Move killer;
	S16 score;
};

struct TTEntry {
	U64 key;
	Move move;
	U8 flag;
	S16 score;
	U8 depth;
};

struct SearchInfo {
	bool post;
	bool stop;
	int depthLimit;
	U64 timeStart;
	U64 timeLimit;
	U64 nodes;
	U64 nodesLimit;
}info;

U64 ranksBB[8] = {
	0x00000000000000ffULL,
	0x000000000000ff00ULL,
	0x0000000000ff0000ULL,
	0x00000000ff000000ULL,
	0x000000ff00000000ULL,
	0x0000ff0000000000ULL,
	0x00ff000000000000ULL,
	0xff00000000000000ULL };

U64 filesBB[8] = {
	0x0101010101010101ULL,
	0x0202020202020202ULL,
	0x0404040404040404ULL,
	0x0808080808080808ULL,
	0x1010101010101010ULL,
	0x2020202020202020ULL,
	0x4040404040404040ULL,
	0x8080808080808080ULL };

const U64 tt_count = 64ULL << 15;
const int material[7] = { 100,320,330,500,900,0,0 };
const int insufVal[PT_NB] = { 5,2,3,5,5,0 };
U64 keys[848];
Stack stack[MAX_PLY]{};
S32 hh_table[2][2][64][64]{};
TTEntry tt[tt_count]{};
int hash_count = 0;
U64 hash_history[1024]{};
int factors[6]{};

struct Options {
	string factors = "16,14,16,16,17,16";
}options;

void UciCommand(Position& pos, string command);

static bool operator==(const Move& lhs, const Move& rhs) { return !memcmp(&rhs, &lhs, sizeof(Move)); }

static inline void TTClear() { memset(tt, 0, sizeof tt); }
static inline U64 Flip(const U64 bb) { return _byteswap_uint64(bb); }
static inline U64 GetTimeMs() { return GetTickCount64(); }

//Returns the index of the least significant bit of bb, or undefined if bb is 0.
static inline int LSB(const U64 bb) {
	return (int)_tzcnt_u64(bb);
}

static inline int Count(const U64 bb) {
	return (int)_mm_popcnt_u64(bb);
}

static inline U64 East(const U64 bb) {
	return (bb << 1) & ~0x0101010101010101ULL;
}

static inline U64 West(const U64 bb) {
	return (bb >> 1) & ~0x8080808080808080ULL;
}

static inline U64 North(const U64 bb) {
	return bb << 8;
}

static inline U64 South(const U64 bb) {
	return bb >> 8;
}

static inline U64 NW(const U64 bb) {
	return North(West(bb));
}

static inline U64 NE(const U64 bb) {
	return North(East(bb));
}

static inline U64 SW(const U64 bb) {
	return South(West(bb));
}

static inline U64 SE(const U64 bb) {
	return South(East(bb));
}

static bool IsRepetition(Position& pos, U64 hash) {
	int limit = max(0, hash_count - pos.move50);
	for (int n = hash_count - 4; n >= limit; n -= 2)
		if (hash_history[n] == hash)
			return true;
	return false;
}

static void FlipPosition(Position& pos) {
	pos.color[0] = Flip(pos.color[0]);
	pos.color[1] = Flip(pos.color[1]);
	for (int i = 0; i < 6; ++i)
		pos.pieces[i] = Flip(pos.pieces[i]);
	pos.ep = Flip(pos.ep);
	swap(pos.color[0], pos.color[1]);
	swap(pos.castling[0], pos.castling[2]);
	swap(pos.castling[1], pos.castling[3]);
	pos.flipped = !pos.flipped;
}

static string SquareToUci(const int sq, const int flip) {
	string str;
	str += 'a' + (sq % 8);
	str += '1' + (flip ? (7 - sq / 8) : (sq / 8));
	return str;
}

static string MoveToUci(const Move& move, const int flip) {
	string str = SquareToUci(move.from, flip) + SquareToUci(move.to, flip);
	if (move.promo != PT_NB)
		str += "\0nbrq\0\0"[move.promo];
	return str;
}

static Move UciToMove(string& uci, int flip) {
	Move m;
	m.from = (uci[0] - 'a');
	int f = (uci[1] - '1');
	m.from += 8 * (flip ? 7 - f : f);
	m.to = (uci[2] - 'a');
	f = (uci[3] - '1');
	m.to += 8 * (flip ? 7 - f : f);
	m.promo = PT_NB;
	switch (uci[4]) {
	case 'N':
	case 'n':
		m.promo = KNIGHT;
		break;
	case 'B':
	case 'b':
		m.promo = BISHOP;
		break;
	case 'R':
	case 'r':
		m.promo = ROOK;
		break;
	case 'Q':
	case 'q':
		m.promo = QUEEN;
		break;
	}
	return m;
}

static int PieceTypeOn(const Position& pos, const int sq) {
	const U64 bb = 1ULL << sq;
	for (int i = 0; i < PT_NB; ++i) {
		if (pos.pieces[i] & bb) {
			return i;
		}
	}
	return PT_NB;
}

static void ResetInfo() {
	info.post = true;
	info.stop = false;
	info.nodes = 0;
	info.depthLimit = MAX_PLY;
	info.nodesLimit = 0;
	info.timeLimit = 0;
	info.timeStart = GetTimeMs();
}


template <typename F>
U64 Ray(const U64 bb, const U64 blockers, F f) {
	U64 mask = f(bb);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	return mask;
}

static U64 BbKnightAttack(const U64 bb) {
	return (((bb << 15) | (bb >> 17)) & 0x7F7F7F7F7F7F7F7FULL) | (((bb << 17) | (bb >> 15)) & 0xFEFEFEFEFEFEFEFEULL) |
		(((bb << 10) | (bb >> 6)) & 0xFCFCFCFCFCFCFCFCULL) | (((bb << 6) | (bb >> 10)) & 0x3F3F3F3F3F3F3F3FULL);
}

static U64 KnightAttack(const int sq, const U64) {
	return BbKnightAttack(1ULL << sq);
}

static U64 BbBishopAttack(const U64 bb, const U64 blockers) {
	return Ray(bb, blockers, NW) | Ray(bb, blockers, NE) | Ray(bb, blockers, SW) | Ray(bb, blockers, SE);
}

static U64 BishopAttack(const int sq, const U64 blockers) {
	return BbBishopAttack(1ULL << sq, blockers);
}

static U64 BbRookAttack(const U64 bb, const U64 blockers) {
	return Ray(bb, blockers, North) | Ray(bb, blockers, East) | Ray(bb, blockers, South) | Ray(bb, blockers, West);
}

static U64 RookAttack(const int sq, const U64 blockers) {
	return BbRookAttack(1ULL << sq, blockers);
}

static U64 KingAttack(const int sq, const U64) {
	const U64 bb = 1ULL << sq;
	return (bb << 8) | (bb >> 8) |
		(((bb >> 1) | (bb >> 9) | (bb << 7)) & 0x7F7F7F7F7F7F7F7FULL) |
		(((bb << 1) | (bb << 9) | (bb >> 7)) & 0xFEFEFEFEFEFEFEFEULL);
}

static bool IsAttacked(const Position& pos, const int sq, const int them = true) {
	const U64 bb = 1ULL << sq;
	const U64 kt = pos.color[them] & pos.pieces[KNIGHT];
	const U64 BQ = pos.pieces[BISHOP] | pos.pieces[QUEEN];
	const U64 RQ = pos.pieces[ROOK] | pos.pieces[QUEEN];
	const U64 pawns = pos.color[them] & pos.pieces[PAWN];
	const U64 pawn_attacks = them ? SW(pawns) | SE(pawns) : NW(pawns) | NE(pawns);
	return (pawn_attacks & bb) | (kt & KnightAttack(sq, 0)) |
		(BishopAttack(sq, pos.color[0] | pos.color[1]) & pos.color[them] & BQ) |
		(RookAttack(sq, pos.color[0] | pos.color[1]) & pos.color[them] & RQ) |
		(KingAttack(sq, 0) & pos.color[them] & pos.pieces[KING]);
}

static bool MakeMove(Position& pos, const Move& move) {
	const int piece = PieceTypeOn(pos, move.from);
	const int captured = PieceTypeOn(pos, move.to);
	const U64 to = 1ULL << move.to;
	const U64 from = 1ULL << move.from;
	pos.move50++;
	if (captured != PT_NB || piece == PAWN)
		pos.move50 = 0;
	pos.color[0] ^= from | to;
	pos.pieces[piece] ^= from | to;
	if (piece == PAWN && to == pos.ep) {
		pos.color[1] ^= to >> 8;
		pos.pieces[PAWN] ^= to >> 8;
	}
	pos.ep = 0x0ULL;
	if (piece == PAWN && move.to - move.from == 16) {
		pos.ep = to >> 8;
	}
	if (captured != PT_NB) {
		pos.color[1] ^= to;
		pos.pieces[captured] ^= to;
	}
	if (piece == KING) {
		const U64 bb = move.to - move.from == 2 ? 0xa0ULL : move.to - move.from == -2 ? 0x9ULL : 0x0ULL;
		pos.color[0] ^= bb;
		pos.pieces[ROOK] ^= bb;
	}
	if (piece == PAWN && move.to >= 56) {
		pos.pieces[PAWN] ^= to;
		pos.pieces[move.promo] ^= to;
	}
	pos.castling[0] &= ((from | to) & 0x90ULL) == 0;
	pos.castling[1] &= ((from | to) & 0x11ULL) == 0;
	pos.castling[2] &= ((from | to) & 0x9000000000000000ULL) == 0;
	pos.castling[3] &= ((from | to) & 0x1100000000000000ULL) == 0;
	FlipPosition(pos);
	return !IsAttacked(pos, (int)LSB(pos.color[1] & pos.pieces[KING]), false);
}

static void AddMove(Move* const moveList, int& num_moves, const U8 from, const U8 to, const U8 promo = PT_NB) {
	moveList[num_moves++] = Move{ from, to, promo };
}

static void GeneratePawnMoves(Move* const moveList, int& num_moves, U64 to_mask, const int offset) {
	while (to_mask) {
		const int to = (int)LSB(to_mask);
		to_mask &= to_mask - 1;
		if (to >= 56) {
			AddMove(moveList, num_moves, to + offset, to, KNIGHT);
			AddMove(moveList, num_moves, to + offset, to, BISHOP);
			AddMove(moveList, num_moves, to + offset, to, ROOK);
			AddMove(moveList, num_moves, to + offset, to, QUEEN);
		}
		else
			AddMove(moveList, num_moves, to + offset, to);
	}
}

static void GeneratePieceMoves(Move* const moveList, int& num_moves, const Position& pos, const int piece, const U64 to_mask, U64(*func)(int, U64)) {
	U64 copy = pos.color[0] & pos.pieces[piece];
	while (copy) {
		const int fr = LSB(copy);
		copy &= copy - 1;
		U64 moves = func(fr, pos.color[0] | pos.color[1]) & to_mask;
		while (moves) {
			const int to = LSB(moves);
			moves &= moves - 1;
			AddMove(moveList, num_moves, fr, to);
		}
	}
}

static int MoveGen(const Position& pos, Move* const moveList, const bool only_captures) {
	int num_moves = 0;
	const U64 all = pos.color[0] | pos.color[1];
	const U64 to_mask = only_captures ? pos.color[1] : ~pos.color[0];
	const U64 pawns = pos.color[0] & pos.pieces[PAWN];
	GeneratePawnMoves(
		moveList, num_moves, North(pawns) & ~all & (only_captures ? 0xFF00000000000000ULL : 0xFFFFFFFFFFFF0000ULL), -8);
	if (!only_captures) {
		GeneratePawnMoves(moveList, num_moves, North(North(pawns & 0xFF00ULL) & ~all) & ~all, -16);
	}
	GeneratePawnMoves(moveList, num_moves, NW(pawns) & (pos.color[1] | pos.ep), -7);
	GeneratePawnMoves(moveList, num_moves, NE(pawns) & (pos.color[1] | pos.ep), -9);
	GeneratePieceMoves(moveList, num_moves, pos, KNIGHT, to_mask, KnightAttack);
	GeneratePieceMoves(moveList, num_moves, pos, BISHOP, to_mask, BishopAttack);
	GeneratePieceMoves(moveList, num_moves, pos, QUEEN, to_mask, BishopAttack);
	GeneratePieceMoves(moveList, num_moves, pos, ROOK, to_mask, RookAttack);
	GeneratePieceMoves(moveList, num_moves, pos, QUEEN, to_mask, RookAttack);
	GeneratePieceMoves(moveList, num_moves, pos, KING, to_mask, KingAttack);
	if (!only_captures && pos.castling[0] && !(all & 0x60ULL) && !IsAttacked(pos, 4) && !IsAttacked(pos, 5)) {
		AddMove(moveList, num_moves, 4, 6);
	}
	if (!only_captures && pos.castling[1] && !(all & 0xEULL) && !IsAttacked(pos, 4) && !IsAttacked(pos, 3)) {
		AddMove(moveList, num_moves, 4, 2);
	}
	return num_moves;
}

static constexpr U64 Attacks(int pt, int sq, U64 blockers) {
	switch (pt) {
	case ROOK:
		return RookAttack(sq, blockers);
	case BISHOP:
		return BishopAttack(sq, blockers);
	case QUEEN:
		return RookAttack(sq, blockers) | BishopAttack(sq, blockers);
	case KNIGHT:
		return KnightAttack(sq, blockers);
	case KING:
		return KingAttack(sq, blockers);
	default:
		return 0;
	}
}

static auto GetHash(const Position& pos) {
	U64 hash = 0;
	for (S32 p = PAWN; p < PT_NB; ++p) {
		U64 copy = pos.pieces[p] & pos.color[0];
		while (copy) {
			const S32 sq = LSB(copy);
			copy &= copy - 1;
			hash ^= keys[p * 64 + sq];
		}
		copy = pos.pieces[p] & pos.color[1];
		while (copy) {
			const S32 sq = LSB(copy);
			copy &= copy - 1;
			hash ^= keys[p * 64 + sq + 6 * 64];
		}
	}
	if (pos.ep)
		hash ^= keys[12 * 64 + LSB(pos.ep)];
	hash ^= keys[13 * 64 + pos.castling[0] + pos.castling[1] * 2 + pos.castling[2] * 4 + pos.castling[3] * 8];
	return hash;
}

static bool InputAvailable() {
	static HANDLE hstdin = 0;
	static bool pipe = false;
	unsigned long dw = 0;
	if (!hstdin) {
		hstdin = GetStdHandle(STD_INPUT_HANDLE);
		pipe = !GetConsoleMode(hstdin, &dw);
		if (!pipe)
		{
			SetConsoleMode(hstdin, dw & ~(ENABLE_MOUSE_INPUT | ENABLE_WINDOW_INPUT));
			FlushConsoleInputBuffer(hstdin);
		}
		else
		{
			setvbuf(stdin, NULL, _IONBF, 0);
			setvbuf(stdout, NULL, _IONBF, 0);
		}
	}
	if (pipe)
		PeekNamedPipe(hstdin, 0, 0, 0, &dw, 0);
	else
		GetNumberOfConsoleInputEvents(hstdin, &dw);
	return dw > 1;
}

static bool CheckUp(Position& pos) {
	if ((++info.nodes & 0xffff) == 0) {
		if (info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit)
			info.stop = true;
		if (info.nodesLimit && info.nodes > info.nodesLimit)
			info.stop = true;
		if (InputAvailable()) {
			string line;
			getline(cin, line);
			UciCommand(pos, line);
		}
	}
	return info.stop;
}

static bool IsPseudolegalMove(const Position& pos, const Move& move) {
	Move moves[256];
	const int num_moves = MoveGen(pos, moves, false);
	for (int i = 0; i < num_moves; ++i)
		if (moves[i] == move)
			return true;
	return false;
}

static void PrintPv(const Position& pos, const Move move) {
	if (!IsPseudolegalMove(pos, move))
		return;
	auto npos = pos;
	if (!MakeMove(npos, move))
		return;
	cout << " " << MoveToUci(move, pos.flipped);
	const U64 tt_key = GetHash(npos);
	const TTEntry& tt_entry = tt[tt_key % tt_count];
	if (tt_entry.key != tt_key)
		return;
	if (IsRepetition(npos, tt_key))
		return;
	hash_history[hash_count++] = tt_key;
	PrintPv(npos, tt_entry.move);
	hash_count--;
}

static int Popcount(const U64 bb) {
	return (int)__popcnt64(bb);
}

static int Permill() {
	int pm = 0;
	for (int n = 0; n < 1000; n++)
		if (tt[n].key)
			pm++;
	return pm;
}

//prints the bitboard
static void PrintBitboard(U64 bb) {
	const char* s = "   +---+---+---+---+---+---+---+---+\n";
	const char* t = "     A   B   C   D   E   F   G   H\n";
	cout << t;
	for (int i = 56; i >= 0; i -= 8) {
		cout << s << " " << i / 8 + 1 << " ";
		for (int x = 0; x < 8; x++) {
			const char* c = 1LL << (i + x) & bb ? "x" : " ";
			cout << "| " << c << " ";
		}
		cout << "| " << i / 8 + 1 << endl;
	}
	cout << s;
	cout << t << endl;
}

static int EvalPosition(Position& pos) {
	int score = 0;
	int insufficient[2]{};
	U64 bbBlockers = pos.color[0] | pos.color[1];
	for (S32 c = WHITE; c < COLOR_NB; ++c) {
		for (int pt = PAWN; pt < KING; ++pt) {
			int count = Count(pos.color[0] & pos.pieces[pt]);
			score += material[pt] * count;
			insufficient[c] += insufVal[pt] * count;
		}
		U64 bbStart1 = pos.color[1] & pos.pieces[PAWN];
		U64 bbControl1 = SW(bbStart1) | SE(bbStart1);
		score -= Count(bbControl1) * factors[0] / 8;
		U64 bbStart0 = pos.color[0] & pos.pieces[KNIGHT];
		U64 bbAttack0 = BbKnightAttack(bbStart0) & ~bbControl1;
		score += Count(bbAttack0) * factors[1] / 8;
		bbStart0 = pos.color[0] & (pos.pieces[BISHOP] | pos.pieces[QUEEN]);
		bbAttack0 = BbBishopAttack(bbStart0, bbBlockers) & ~bbControl1;
		score += Count(bbAttack0) * factors[2] / 8;
		bbStart0 = pos.color[0] & (pos.pieces[ROOK] | pos.pieces[QUEEN]);
		bbAttack0 = BbRookAttack(bbStart0, bbBlockers) & ~bbControl1;
		score += Count(bbAttack0) * factors[3] / 8;
		bbStart0 = pos.color[0] & pos.pieces[KING];
		U64 file0 = filesBB[LSB(bbStart0) % 8];
		file0 |= East(file0) | West(file0);
		bbAttack0 = file0 & (ranksBB[1] | ranksBB[2]) & ~(filesBB[3] | filesBB[4]);
		bbAttack0 &= (pos.color[0] & pos.pieces[PAWN]);
		score += Count(bbAttack0) * factors[4] / 8;
		score += Count(bbAttack0 & ranksBB[1]) * factors[5] / 8;
		FlipPosition(pos);
		score = -score;
	}
	if (max(insufficient[0], insufficient[1]) < 5)
		return 0;
	if (insufficient[score < 0] < 4)
		return 0;
	return (100 - pos.move50) * score / 100;
}

static int SearchAlpha(Position& pos, int alpha, int beta, int depth, const int ply, Stack* const stack, const bool doNull = true) {
	if (CheckUp(pos))
		return 0;
	int  mate_value = MATE - ply;
	if (alpha < -mate_value) alpha = -mate_value;
	if (beta > mate_value - 1) beta = mate_value - 1;
	if (alpha >= beta) return alpha;
	int staticEval = EvalPosition(pos);
	if (ply >= MAX_PLY)
		return staticEval;
	stack[ply].score = staticEval;
	const S32 in_check = IsAttacked(pos, LSB(pos.color[0] & pos.pieces[KING]));
	depth += in_check;

	bool inQuiescence = depth < 1;
	const U64 tt_key = GetHash(pos);

	if (ply && (pos.move50 > 99 || IsRepetition(pos, tt_key)))
		return 0;
	TTEntry& tt_entry = tt[tt_key % tt_count];
	Move tt_move{};
	if (tt_entry.key == tt_key) {
		tt_move = tt_entry.move;
		if (alpha == beta - 1 && tt_entry.depth >= depth) {
			if (tt_entry.flag == EXACT)
				return tt_entry.score;
			if (tt_entry.flag == LOWER && tt_entry.score <= alpha)
				return tt_entry.score;
			if (tt_entry.flag == UPPER && tt_entry.score >= beta)
				return tt_entry.score;
		}
	}
	else
		depth -= depth > 3;

	const bool improving = ply > 1 && staticEval > stack[ply - 2].score;

	// If static_eval > tt_entry.score, tt_entry.flag cannot be Lower (ie must be Upper or Exact).
	// Otherwise, tt_entry.flag cannot be Upper (ie must be Lower or Exact).
	if (tt_entry.key == tt_key && tt_entry.flag != staticEval > tt_entry.score)
		staticEval = tt_entry.score;

	if (inQuiescence && alpha < staticEval) {
		alpha = staticEval;
		if (alpha >= beta)
			return beta;
	}

	if (ply > 0 && !inQuiescence && !in_check && alpha == beta - 1) {
		// Reverse futility pruning
		if (depth < 8) {
			if (staticEval - 71 * (depth - improving) >= beta)
				return staticEval;

			inQuiescence = staticEval + 238 * depth < alpha;
		}

		// Null move pruning
		if (depth > 2 && staticEval >= beta && staticEval >= stack[ply].score && doNull &&
			pos.color[0] & ~pos.pieces[PAWN] & ~pos.pieces[KING]) {
			Position npos = pos;
			FlipPosition(npos);
			npos.ep = 0;
			if (-SearchAlpha(npos,
				-beta,
				-alpha,
				depth - 4 - depth / 5 - min((staticEval - beta) / 196, 3),
				ply + 1,
				stack,
				false) >= beta)
				return beta;
		}
	}

	hash_history[hash_count++] = tt_key;
	U8 tt_flag = LOWER;

	S32 num_moves_evaluated = 0;
	S32 num_moves_quiets = 0;
	S32 best_score = inQuiescence ? staticEval : -INF;
	auto best_move = tt_move;

	auto& moves = stack[ply].moves;
	auto& moves_scores = stack[ply].moves_scores;
	auto& moves_evaluated = stack[ply].moves_evaluated;
	const S32 num_moves = MoveGen(pos, moves, inQuiescence);

	for (S32 i = 0; i < num_moves; ++i) {
		// Score moves at the first loop, except if we have a hash move,
		// then we'll use that first and delay sorting one iteration.
		if (i == !(no_move == tt_move))
			for (S32 j = 0; j < num_moves; ++j) {
				const S32 gain = material[moves[j].promo] + material[PieceTypeOn(pos, moves[j].to)];
				moves_scores[j] = hh_table[pos.flipped][!gain][moves[j].from][moves[j].to] +
					(gain || moves[j] == stack[ply].killer) * 2048 + gain;
			}

		// Find best move remaining
		S32 best_move_index = i;
		for (S32 j = i; j < num_moves; ++j) {
			if (moves[j] == tt_move) {
				best_move_index = j;
				break;
			}
			if (moves_scores[j] > moves_scores[best_move_index])
				best_move_index = j;
		}

		const Move move = moves[best_move_index];
		moves[best_move_index] = moves[i];
		moves_scores[best_move_index] = moves_scores[i];

		// Material gain
		const S32 gain = material[move.promo] + material[PieceTypeOn(pos, move.to)];

		// Delta pruning
		if (inQuiescence && !in_check && staticEval + 50 + gain < alpha)
			break;

		// Forward futility pruning
		if (ply > 0 && depth < 8 && !inQuiescence && !in_check && num_moves_evaluated && staticEval + 105 * depth + gain < alpha)
			break;

		Position npos = pos;
		if (!MakeMove(npos, move))
			continue;

		S32 score;
		S32 reduction = depth > 3 && num_moves_evaluated > 1
			? max(num_moves_evaluated / 13 + depth / 14 + (alpha == beta - 1) + !improving -
				min(max(hh_table[pos.flipped][!gain][move.from][move.to] / 128, -2), 2),
				0)
			: 0;

		while (num_moves_evaluated &&
			(score = -SearchAlpha(npos,
				-alpha - 1,
				-alpha,
				depth - reduction - 1,
				ply + 1,
				stack)) > alpha &&
			reduction > 0)
			reduction = 0;

		if (!num_moves_evaluated || score > alpha && score < beta)
			score = -SearchAlpha(npos,
				-beta,
				-alpha,
				depth - 1,
				ply + 1,
				stack);
		if (info.stop)
			break;

		if (score > best_score)
			best_score = score;

		if (score > alpha) {
			best_move = move;
			tt_flag = EXACT;
			alpha = score;
			stack[ply].move = move;
			if (!ply && info.post) {
				cout << "info depth " << depth << " score ";
				if (abs(score) < MATE - MAX_PLY)
					cout << "cp " << score;
				else
					cout << "mate " << (score > 0 ? (MATE - score + 1) >> 1 : -(MATE + score) >> 1);
				const U64 elapsed = GetTimeMs() - info.timeStart;
				cout << " time " << elapsed;
				cout << " nodes " << info.nodes;
				cout << " hashfull " << Permill() << " pv";
				PrintPv(pos, stack[0].move);
				cout << endl;
			}
			if (score >= beta) {
				tt_flag = UPPER;

				if (!gain)
					stack[ply].killer = move;

				hh_table[pos.flipped][!gain][move.from][move.to] +=
					depth * depth - depth * depth * hh_table[pos.flipped][!gain][move.from][move.to] / 512;
				for (S32 j = 0; j < num_moves_evaluated; ++j) {
					const S32 prev_gain = material[moves_evaluated[j].promo] + material[PieceTypeOn(pos, moves_evaluated[j].to)];
					hh_table[pos.flipped][!prev_gain][moves_evaluated[j].from][moves_evaluated[j].to] -=
						depth * depth +
						depth * depth *
						hh_table[pos.flipped][!prev_gain][moves_evaluated[j].from][moves_evaluated[j].to] / 512;
				}
				break;
			}
		}

		moves_evaluated[num_moves_evaluated++] = move;
		if (!gain)
			num_moves_quiets++;
		if ((!in_check) && (alpha == beta - 1) && (num_moves_quiets > (1 + depth * depth) >> (int)!improving))
			break;
	}
	hash_count--;
	if (info.stop)
		return 0;
	if (best_score == -INF)
		return in_check ? ply - MATE : 0;
	tt_entry.key = tt_key;
	tt_entry.move = best_move;
	tt_entry.flag = tt_flag;
	tt_entry.score = best_score;
	tt_entry.depth = max(0, depth);
	return best_score;
}

static void SearchIteratively(Position& pos) {
	info.stop = false;
	info.nodes = 0;
	info.timeStart = GetTimeMs();
	memset(stack, 0, sizeof(stack));
	memset(tt, 0, sizeof(tt));
	for (int depth = 1; depth <= info.depthLimit; ++depth) {
		SearchAlpha(pos, -MATE, MATE, depth, 0, stack);
		if (info.stop)
			break;
		if (info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit / 2)
			break;
	}
	if (info.post)
		cout << "bestmove " << MoveToUci(stack[0].move, pos.flipped) << endl << flush;
}

static inline void PerftDriver(Position pos, int depth) {
	Move list[256];
	const S32 num_moves = MoveGen(pos, list, false);
	for (int n = 0; n < num_moves; n++) {
		Position npos = pos;
		if (!MakeMove(npos, list[n]))
			continue;
		if (depth)
			PerftDriver(npos, depth - 1);
		else
			info.nodes++;
	}
}

static void SetFen(Position& pos, const string& fen) {
	pos.flipped = false;
	pos.ep = 0;
	memset(pos.color, 0, sizeof(pos.color));
	memset(pos.pieces, 0, sizeof(pos.pieces));
	memset(pos.castling, 0, sizeof(pos.castling));
	stringstream ss(fen);
	string word;
	ss >> word;
	int i = 56;
	for (const auto c : word) {
		if (c >= '1' && c <= '8')
			i += c - '1' + 1;
		else if (c == '/')
			i -= 16;
		else {
			const int side = c == 'p' || c == 'n' || c == 'b' || c == 'r' || c == 'q' || c == 'k';
			const int piece = (c == 'p' || c == 'P') ? PAWN
				: (c == 'n' || c == 'N') ? KNIGHT
				: (c == 'b' || c == 'B') ? BISHOP
				: (c == 'r' || c == 'R') ? ROOK
				: (c == 'q' || c == 'Q') ? QUEEN
				: KING;
			pos.color[side] ^= 1ULL << i;
			pos.pieces[piece] ^= 1ULL << i;
			i++;
		}
	}
	ss >> word;
	const bool black_move = word == "b";
	ss >> word;
	for (const auto c : word) {
		pos.castling[0] |= c == 'K';
		pos.castling[1] |= c == 'Q';
		pos.castling[2] |= c == 'k';
		pos.castling[3] |= c == 'q';
	}
	ss >> word;
	if (word != "-") {
		const int sq = word[0] - 'a' + 8 * (word[1] - '1');
		pos.ep = 1ULL << sq;
	}
	ss >> word;
	pos.move50 = stoi(word);
	if (black_move)
		FlipPosition(pos);
}

static int ShrinkNumber(U64 n) {
	if (n < 10000)
		return 0;
	if (n < 10000000)
		return 1;
	if (n < 10000000000)
		return 2;
	return 3;
}

//displays a summary
static void PrintSummary(U64 time, U64 nodes) {
	U64 nps = (nodes * 1000) / max(time, 1ull);
	const char* units[] = { "", "k", "m", "g" };
	int sn = ShrinkNumber(nps);
	U64 p = (int)pow(10, sn * 3);
	printf("-----------------------------\n");
	printf("Time        : %llu\n", time);
	printf("Nodes       : %llu\n", nodes);
	printf("Nps         : %llu (%llu%s/s)\n", nps, nps / p, units[sn]);
	printf("-----------------------------\n");
}

static void PrintPerformanceHeader() {
	printf("-----------------------------\n");
	printf("ply      time        nodes\n");
	printf("-----------------------------\n");
}

//start benchmark
static void UciBench(Position& pos) {
	ResetInfo();
	PrintPerformanceHeader();
	info.depthLimit = 0;
	info.post = false;
	U64 elapsed = 0;
	while (elapsed < 3000) {
		++info.depthLimit;
		SearchIteratively(pos);
		elapsed = GetTimeMs() - info.timeStart;
		printf(" %2d. %8llu %12llu\n", info.depthLimit, elapsed, info.nodes);
	}
	PrintSummary(elapsed, info.nodes);
}

//start performance test
static void UciPerformance(Position& pos) {
	ResetInfo();
	PrintPerformanceHeader();
	info.depthLimit = 0;
	S64 elapsed = 0;
	while (elapsed < 3000) {
		PerftDriver(pos, info.depthLimit++);
		elapsed = GetTimeMs() - info.timeStart;
		printf(" %2d. %8llu %12llu\n", info.depthLimit, elapsed, info.nodes);
	}
	PrintSummary(elapsed, info.nodes);
}

static void PrintBoard(Position& pos) {
	Position npos = pos;
	if (npos.flipped)
		FlipPosition(npos);
	const char* s = "   +---+---+---+---+---+---+---+---+\n";
	const char* t = "     A   B   C   D   E   F   G   H\n";
	cout << t;
	for (int i = 56; i >= 0; i -= 8) {
		cout << s << " " << i / 8 + 1 << " ";
		for (int j = 0; j < 8; j++) {
			int sq = i + j;
			int piece = PieceTypeOn(npos, sq);
			if (npos.color[0] & 1ull << sq)
				cout << "| " << "ANBRQK "[piece] << " ";
			else
				cout << "| " << "anbrqk "[piece] << " ";
		}
		cout << "| " << i / 8 + 1 << endl;
	}
	cout << s;
	cout << t << endl;
	char castling[5] = "KQkq";
	for (int n = 0; n < 4; n++)
		if (!npos.castling[n])
			castling[n] = '-';
	printf("side     : %16s\n", pos.flipped ? "black" : "white");
	printf("castling : %16s\n", castling);
	printf("hash     : %16llx\n", GetHash(pos));
}

static void ParsePosition(Position& pos, string command) {
	string fen = START_FEN;
	stringstream ss(command);
	string token;
	ss >> token;
	if (token != "position")
		return;
	ss >> token;
	if (token == "startpos")
		ss >> token;
	else if (token == "fen") {
		fen = "";
		while (ss >> token && token != "moves")
			fen += token + " ";
		fen.pop_back();
	}
	SetFen(pos, fen);
	hash_count = 0;
	while (ss >> token) {
		Move m = UciToMove(token, pos.flipped);
		if (PieceTypeOn(pos, m.to) != PT_NB || PieceTypeOn(pos, m.from) == PAWN)
			hash_count = 0;
		hash_history[hash_count++] = GetHash(pos);
		MakeMove(pos, m);
	}
}

static void ParseGo(Position& pos, string command) {
	stringstream ss(command);
	string token;
	ss >> token;
	if (token != "go")
		return;
	ResetInfo();
	int wtime = 0;
	int btime = 0;
	int winc = 0;
	int binc = 0;
	int movestogo = 32;
	while (ss >> token) {
		if (token == "wtime")
			ss >> wtime;
		else if (token == "btime")
			ss >> btime;
		else if (token == "winc")
			ss >> winc;
		else if (token == "binc")
			ss >> binc;
		else if (token == "movestogo")
			ss >> movestogo;
		else if (token == "movetime")
			ss >> info.timeLimit;
		else if (token == "depth")
			ss >> info.depthLimit;
		else if (token == "nodes")
			ss >> info.nodesLimit;
	}
	int time = pos.flipped ? btime : wtime;
	int inc = pos.flipped ? binc : winc;
	if (time)
		info.timeLimit = max(1, min(time / movestogo + inc, time / 2));
	SearchIteratively(pos);
}

static void SplitInt(const string& txt, vector<int>& vInt, char ch) {
	vInt.clear();
	if (txt == "")
		return;
	size_t pos = txt.find(ch);
	size_t initialPos = 0;
	while (pos != std::string::npos) {
		vInt.push_back(stoi(txt.substr(initialPos, pos - initialPos)));
		initialPos = pos + 1;

		pos = txt.find(ch, initialPos);
	}
	vInt.push_back(stoi(txt.substr(initialPos, min(pos, txt.size()) - initialPos + 1)));
}

static void InitFactors() {
	vector<int> split{};
	SplitInt(options.factors, split, ',');
	for (int n = 0; n < split.size(); n++)
		factors[n] = split[n];
}

void UciCommand(Position& pos, string command) {
	if (command.empty())
		return;
	stringstream ss(command);
	string token;
	ss >> token;
	if (token == "uci") {
		cout << "id name " << NAME << endl;
		cout << "option name factors type string default " << options.factors << endl;
		cout << "uciok" << endl;
	}
	else if (token == "setoption") {
		ss >> token;//name
		ss >> token;
		if (token == "factors") {
			ss >> token;//value
			ss >> options.factors;
			InitFactors();
		}
	}
	else if (token == "isready")cout << "readyok" << endl;
	else if (token == "ucinewgame")memset(hh_table, 0, sizeof(hh_table));
	else if (token == "bench")UciBench(pos);
	else if (token == "perft")UciPerformance(pos);
	else if (token == "print")PrintBoard(pos);
	else if (token == "stop")info.stop = true;
	else if (token == "quit")exit(0);
	else if (token == "position")ParsePosition(pos, command);
	else if (token == "go")ParseGo(pos, command);
}

static void UciLoop(Position& pos) {
	string line;
	while (true) {
		getline(cin, line);
		UciCommand(pos, line);
	}
}

static void InitHash() {
	mt19937_64 r;
	for (U64& k : keys)
		k = r();
}

int main(const int argc, const char** argv) {
	Position pos;
	cout << NAME << " " << VERSION << endl;
	InitHash();
	InitFactors();
	SetFen(pos, START_FEN);
	UciLoop(pos);
}
