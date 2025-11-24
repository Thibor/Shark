#include <iostream>
#include <vector>
#include <sstream> 

#define MATE_VALUE (1 << 15)
#define MAX_DEPTH 100
#define INF (1 << 16)
#define U16 unsigned __int16
#define S32 signed __int32
#define S64 signed __int64
#define U64 unsigned __int64
#define NAME "Shark"
#define VERSION "2025-10-13"
#define DEFAULT_FEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
#define RAND_64 ((U64)rand() | (U64)rand() << 15 | (U64)rand() << 30 | (U64)rand() << 45 |((U64)rand() & 0xf) << 60 )

using namespace std;

enum Color { WHITE, BLACK, COLOR_NB };
enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };
enum Bound { exact, lowerbound, upperbound };

struct Position {
	int castling[4] = { true, true, true, true };
	U64 color[2] = { 0xFFFFULL, 0xFFFF000000000000ULL };
	U64 pieces[6] = { 0xFF00000000FF00ULL,0x4200000000000042ULL,0x2400000000000024ULL,0x8100000000000081ULL,0x800000000000008ULL,0x1000000000000010ULL };
	U64 ep = 0x0ULL;
	int score = 0;
	bool flipped = false;
}pos;

struct Move {
	int from = 0;
	int to = 0;
	int promo = 0;
};

const Move no_move{};

struct Stack {
	Move move;
	Move killer;
	int score;
};

struct TT_Entry {
	U64 key;
	Move move;
	int score;
	int depth;
	U16 flag;
};

struct SSearchInfo {
	bool stop = false;
	int depthLimit = MAX_DEPTH;
	S64 timeStart = 0;
	S64 timeLimit = 0;
	U64 nodes = 0;
	U64 nodesLimit = 0;
}info;

constexpr U64 FileABB = 0x0101010101010101ULL;
constexpr U64 FileBBB = FileABB << 1;
constexpr U64 FileCBB = FileABB << 2;
constexpr U64 FileDBB = FileABB << 3;
constexpr U64 FileEBB = FileABB << 4;
constexpr U64 FileFBB = FileABB << 5;
constexpr U64 FileGBB = FileABB << 6;
constexpr U64 FileHBB = FileABB << 7;

constexpr U64 Rank1BB = 0xFF;
constexpr U64 Rank2BB = Rank1BB << (8 * 1);
constexpr U64 Rank3BB = Rank1BB << (8 * 2);
constexpr U64 Rank4BB = Rank1BB << (8 * 3);
constexpr U64 Rank5BB = Rank1BB << (8 * 4);
constexpr U64 Rank6BB = Rank1BB << (8 * 5);
constexpr U64 Rank7BB = Rank1BB << (8 * 6);
constexpr U64 Rank8BB = Rank1BB << (8 * 7);

U64 bbCenter1 = (FileDBB | FileEBB) & (Rank4BB | Rank5BB);
U64 bbCenter2 = (FileCBB | FileDBB | FileEBB | FileFBB) & (Rank3BB | Rank4BB | Rank5BB | Rank6BB);
U64 bbCenter3 = (FileBBB | FileCBB | FileDBB | FileEBB | FileFBB | FileGBB) & (Rank2BB | Rank3BB | Rank4BB | Rank5BB | Rank6BB | Rank7BB);

const U64 num_tt_entries = 64ULL << 15;  // The first value is the size in megabytes
int materialValOrg[PT_NB] = { 100,320,330,500,900,0 };
U64 keys[848];
Stack stack[128]{};
int64_t hh_table[2][64][64]{};
TT_Entry transposition_table[num_tt_entries] = {};
vector<U64> hash_history;

static void TranspositionClear() {
	memset(hh_table, 0, sizeof(hh_table));
	memset(stack, 0, sizeof(stack));
	memset(transposition_table, 0, sizeof(transposition_table));
}

static S64 GetTimeMs() {
	return (clock() * 1000) / CLOCKS_PER_SEC;
}

static U64 flip(const U64 bb) {
	return _byteswap_uint64(bb);
}

static U64 lsb(const U64 bb) {
	return _tzcnt_u64(bb);
}

static U64 count(const U64 bb) {
	return _mm_popcnt_u64(bb);
}

static U64 East(const U64 bb) {
	return (bb << 1) & ~0x0101010101010101ULL;
}

static U64 West(const U64 bb) {
	return (bb >> 1) & ~0x8080808080808080ULL;
}

static U64 North(const U64 bb) {
	return bb << 8;
}

static U64 South(const U64 bb) {
	return bb >> 8;
}

static U64 nw(const U64 bb) {
	return North(West(bb));
}

static U64 ne(const U64 bb) {
	return North(East(bb));
}

static U64 sw(const U64 bb) {
	return South(West(bb));
}

static U64 se(const U64 bb) {
	return South(East(bb));
}

static void FlipPosition(Position& pos) {
	pos.color[0] = flip(pos.color[0]);
	pos.color[1] = flip(pos.color[1]);
	for (int i = 0; i < 6; ++i) {
		pos.pieces[i] = flip(pos.pieces[i]);
	}
	pos.ep = flip(pos.ep);
	swap(pos.color[0], pos.color[1]);
	swap(pos.castling[0], pos.castling[2]);
	swap(pos.castling[1], pos.castling[3]);
	pos.score = -pos.score;
	pos.flipped = !pos.flipped;
}

auto operator==(const Move& lhs, const Move& rhs) {
	return !memcmp(&rhs, &lhs, sizeof(Move));
}

static string MoveToUci(const Move& move, const int flip) {
	string str;
	str += 'a' + (move.from % 8);
	str += '1' + (flip ? (7 - move.from / 8) : (move.from / 8));
	str += 'a' + (move.to % 8);
	str += '1' + (flip ? (7 - move.to / 8) : (move.to / 8));
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
	for (int i = 0; i < 6; ++i) {
		if (pos.pieces[i] & bb) {
			return i;
		}
	}
	return PT_NB;
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
	return Ray(bb, blockers, nw) | Ray(bb, blockers, ne) | Ray(bb, blockers, sw) | Ray(bb, blockers, se);
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

static bool Attacked(const Position& pos, const int sq, const int them = true) {
	const U64 bb = 1ULL << sq;
	const U64 kt = pos.color[them] & pos.pieces[KNIGHT];
	const U64 BQ = pos.pieces[BISHOP] | pos.pieces[QUEEN];
	const U64 RQ = pos.pieces[ROOK] | pos.pieces[QUEEN];
	const U64 pawns = pos.color[them] & pos.pieces[PAWN];
	const U64 pawn_attacks = them ? sw(pawns) | se(pawns) : nw(pawns) | ne(pawns);
	return (pawn_attacks & bb) | (kt & KnightAttack(sq, 0)) |
		(BishopAttack(sq, pos.color[0] | pos.color[1]) & pos.color[them] & BQ) |
		(RookAttack(sq, pos.color[0] | pos.color[1]) & pos.color[them] & RQ) |
		(KingAttack(sq, 0) & pos.color[them] & pos.pieces[KING]);
}

static auto MakeMove(Position& pos, const Move& move) {
	const int piece = PieceTypeOn(pos, move.from);
	const int captured = PieceTypeOn(pos, move.to);
	const U64 to = 1ULL << move.to;
	const U64 from = 1ULL << move.from;
	pos.color[0] ^= from | to;
	pos.pieces[piece] ^= from | to;
	if (piece == PAWN && to == pos.ep) {
		pos.color[1] ^= to >> 8;
		pos.pieces[PAWN] ^= to >> 8;
		pos.score += materialValOrg[PAWN];
	}

	pos.ep = 0x0ULL;
	if (piece == PAWN && move.to - move.from == 16) {
		pos.ep = to >> 8;
	}
	if (captured != PT_NB) {
		pos.color[1] ^= to;
		pos.pieces[captured] ^= to;
		pos.score += materialValOrg[captured];
	}
	if (piece == KING) {
		const U64 bb = move.to - move.from == 2 ? 0xa0ULL : move.to - move.from == -2 ? 0x9ULL : 0x0ULL;
		pos.color[0] ^= bb;
		pos.pieces[ROOK] ^= bb;
	}
	if (piece == PAWN && move.to >= 56) {
		pos.pieces[PAWN] ^= to;
		pos.pieces[move.promo] ^= to;
		pos.score += materialValOrg[move.promo] - materialValOrg[PAWN];
	}
	pos.castling[0] &= !((from | to) & 0x90ULL);
	pos.castling[1] &= !((from | to) & 0x11ULL);
	pos.castling[2] &= !((from | to) & 0x9000000000000000ULL);
	pos.castling[3] &= !((from | to) & 0x1100000000000000ULL);

	FlipPosition(pos);
	return !Attacked(pos, (int)lsb(pos.color[1] & pos.pieces[KING]), false);
}

static void add_move(Move* const movelist, int& num_moves, const int from, const int to, const int promo = PT_NB) {
	movelist[num_moves++] = Move{ from, to, promo };
}

static void generate_pawn_moves(Move* const movelist, int& num_moves, U64 to_mask, const int offset) {
	while (to_mask) {
		const int to = (int)lsb(to_mask);
		to_mask &= to_mask - 1;
		if (to >= 56) {
			add_move(movelist, num_moves, to + offset, to, QUEEN);
			add_move(movelist, num_moves, to + offset, to, ROOK);
			add_move(movelist, num_moves, to + offset, to, BISHOP);
			add_move(movelist, num_moves, to + offset, to, KNIGHT);
		}
		else {
			add_move(movelist, num_moves, to + offset, to);
		}
	}
}

static void generate_piece_moves(Move* const movelist, int& num_moves, const Position& pos, const int piece, const U64 to_mask, U64(*func)(int, U64)) {
	U64 copy = pos.color[0] & pos.pieces[piece];
	while (copy) {
		const int fr = lsb(copy);
		copy &= copy - 1;
		U64 moves = func(fr, pos.color[0] | pos.color[1]) & to_mask;
		while (moves) {
			const int to = lsb(moves);
			moves &= moves - 1;
			add_move(movelist, num_moves, fr, to);
		}
	}
}

static int MoveGen(const Position& pos, Move* const movelist, const bool only_captures) {
	int num_moves = 0;
	const U64 all = pos.color[0] | pos.color[1];
	const U64 to_mask = only_captures ? pos.color[1] : ~pos.color[0];
	const U64 pawns = pos.color[0] & pos.pieces[PAWN];
	generate_pawn_moves(
		movelist, num_moves, North(pawns) & ~all & (only_captures ? 0xFF00000000000000ULL : 0xFFFFFFFFFFFF0000ULL), -8);
	if (!only_captures) {
		generate_pawn_moves(movelist, num_moves, North(North(pawns & 0xFF00ULL) & ~all) & ~all, -16);
	}
	generate_pawn_moves(movelist, num_moves, nw(pawns) & (pos.color[1] | pos.ep), -7);
	generate_pawn_moves(movelist, num_moves, ne(pawns) & (pos.color[1] | pos.ep), -9);
	generate_piece_moves(movelist, num_moves, pos, KNIGHT, to_mask, KnightAttack);
	generate_piece_moves(movelist, num_moves, pos, BISHOP, to_mask, BishopAttack);
	generate_piece_moves(movelist, num_moves, pos, QUEEN, to_mask, BishopAttack);
	generate_piece_moves(movelist, num_moves, pos, ROOK, to_mask, RookAttack);
	generate_piece_moves(movelist, num_moves, pos, QUEEN, to_mask, RookAttack);
	generate_piece_moves(movelist, num_moves, pos, KING, to_mask, KingAttack);
	if (!only_captures && pos.castling[0] && !(all & 0x60ULL) && !Attacked(pos, 4) && !Attacked(pos, 5)) {
		add_move(movelist, num_moves, 4, 6);
	}
	if (!only_captures && pos.castling[1] && !(all & 0xEULL) && !Attacked(pos, 4) && !Attacked(pos, 3)) {
		add_move(movelist, num_moves, 4, 2);
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
	U64 hash = pos.flipped;
	U64 copy = pos.color[0] | pos.color[1];
	while (copy) {
		const int sq = lsb(copy);
		copy &= copy - 1;
		hash ^= keys[(PieceTypeOn(pos, sq) + 6 * ((pos.color[pos.flipped] >> sq) & 1)) * 64 + sq];
	}
	if (pos.ep)
		hash ^= keys[768 + lsb(pos.ep)];
	hash ^= keys[832 + (pos.castling[0] | pos.castling[1] << 1 | pos.castling[2] << 2 | pos.castling[3] << 3)];
	return hash;
}

static void CheckUp() {
	if ((info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit) || (info.nodesLimit && info.nodes > info.nodesLimit))
		info.stop = true;
}

static bool IsPseudolegalMove(const Position& pos, const Move& move) {
	Move moves[256];
	const int num_moves = MoveGen(pos, moves, false);
	for (int i = 0; i < num_moves; ++i)
		if (moves[i] == move)
			return true;
	return false;
}

static void PrintPv(const Position& pos, const Move move, vector<U64>& hash_history) {
	if (!IsPseudolegalMove(pos, move))
		return;
	auto npos = pos;
	if (!MakeMove(npos, move))
		return;
	cout << " " << MoveToUci(move, pos.flipped);
	const U64 tt_key = GetHash(npos);
	const TT_Entry& tt_entry = transposition_table[tt_key % num_tt_entries];
	if (tt_entry.key != tt_key || tt_entry.move == Move{} || tt_entry.flag != 0) {
		return;
	}
	for (const auto old_hash : hash_history) {
		if (old_hash == tt_key) {
			return;
		}
	}
	hash_history.emplace_back(tt_key);
	PrintPv(npos, tt_entry.move, hash_history);
	hash_history.pop_back();
}

static int Popcount(const U64 bb) {
	return (int)__popcnt64(bb);
}

static int Permill() {
	int pm = 0;
	for (int n = 0; n < 1000; n++) {
		if (transposition_table[n].key)
			pm++;
	}
	return pm;
}

//Prints the bitboard
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
	U64 bbStart0, bbStart1;
	U64 bbMask0, bbMask1;
	U64 control0, control1;
	U64 blockers = pos.color[0] | pos.color[1];

	bbStart0 = pos.color[0] & pos.pieces[PAWN];
	control0 = nw(bbStart0) | ne(bbStart0);
	bbStart1 = pos.color[1] & pos.pieces[PAWN];
	control1 = sw(bbStart1) | se(bbStart1);
	score = Popcount(control0) - Popcount(control1);

	bbStart0 = pos.color[0] & pos.pieces[KNIGHT];
	bbMask0 = BbKnightAttack(bbStart0) & ~control1;
	bbStart1 = pos.color[1] & pos.pieces[KNIGHT];
	bbMask1 = BbKnightAttack(bbStart1) & ~control0;
	bbStart0 = pos.color[0] & pos.pieces[BISHOP];
	bbMask0 |= BbBishopAttack(bbStart0, blockers) & ~control1;
	bbStart1 = pos.color[1] & pos.pieces[BISHOP];
	bbMask1 |= BbBishopAttack(bbStart1, blockers) & ~control0;
	control0 |= bbMask0;
	control1 |= bbMask1;

	bbStart0 = pos.color[0] & pos.pieces[ROOK];
	bbMask0 = BbRookAttack(bbStart0, blockers) & ~control1;
	bbStart1 = pos.color[1] & pos.pieces[ROOK];
	bbMask1 = BbRookAttack(bbStart1, blockers) & ~control0;
	control0 |= bbMask0;
	control1 |= bbMask1;

	bbStart0 = pos.color[0] & pos.pieces[QUEEN];
	bbMask0 = (BbBishopAttack(bbStart0, blockers) | BbRookAttack(bbStart0, blockers)) & ~control1;
	bbStart1 = pos.color[1] & pos.pieces[QUEEN];
	bbMask1 = (BbBishopAttack(bbStart1, blockers) | BbRookAttack(bbStart1, blockers)) & ~control0;
	control0 |= bbMask0;
	control1 |= bbMask1;

	score = Popcount(control0) - Popcount(control1);
	score += Popcount(control0 & bbCenter1) - Popcount(control1 & bbCenter1);
	score += Popcount(control0 & bbCenter2) - Popcount(control1 & bbCenter2);
	score += Popcount(control0 & bbCenter3) - Popcount(control1 & bbCenter3);

	bbStart0 = pos.color[0] & pos.pieces[KING];
	bbStart0 = (nw(bbStart0) | ne(bbStart0) | North(bbStart0)) & ~(FileDBB | FileEBB);
	control0 = bbStart0 & pos.color[0] & pos.pieces[PAWN];
	bbStart1 = pos.color[1] & pos.pieces[KING];
	bbStart1 = sw(bbStart1) | se(bbStart1) | South(bbStart1) & ~(FileDBB | FileEBB);
	control1 = bbStart1 & pos.color[1] & pos.pieces[PAWN];
	score = Popcount(control0) - Popcount(control1);
	bbStart0 |= North(bbStart0);
	bbStart1 |= South(bbStart1);
	control0 = bbStart0 & pos.color[0];
	control1 = bbStart1 & pos.color[1];
	score = Popcount(control0) - Popcount(control1);
	return score;
}

static int SearchAlpha(Position& pos, int alpha, const int beta, int depth, const int ply, Stack* const stack, int64_t(&hh_table)[2][64][64], vector<U64>& hash_history) {
	if ((++info.nodes & 0xffff) == 0)
		CheckUp();
	if (info.stop)
		return 0;
	const int static_eval = pos.score + EvalPosition(pos);
	if (ply > 127)
		return static_eval;
	stack[ply].score = static_eval;
	const auto in_check = Attacked(pos, (int)lsb(pos.color[0] & pos.pieces[KING]));
	depth = in_check ? max(1, depth + 1) : depth;
	const int improving = ply > 1 && static_eval > stack[ply - 2].score;
	int in_qsearch = depth <= 0;
	if (in_qsearch && static_eval > alpha) {
		if (static_eval >= beta)
			return beta;
		alpha = static_eval;
	}
	const U64 tt_key = GetHash(pos);
	if (ply > 0 && !in_qsearch)
		for (const auto old_hash : hash_history)
			if (old_hash == tt_key)
				return 0;
	TT_Entry& tt_entry = transposition_table[tt_key % num_tt_entries];
	Move tt_move{};
	if (tt_entry.key == tt_key) {
		tt_move = tt_entry.move;
		if (ply > 0 && tt_entry.depth >= depth) {
			if (tt_entry.flag == 0)
				return tt_entry.score;
			if (tt_entry.flag == 1 && tt_entry.score <= alpha)
				return tt_entry.score;
			if (tt_entry.flag == 2 && tt_entry.score >= beta)
				return tt_entry.score;
		}
	}
	else if (depth > 3)
		depth--;
	Move moves[256];
	const int num_moves = MoveGen(pos, moves, in_qsearch);
	int64_t move_scores[256];
	for (int j = 0; j < num_moves; ++j) {
		const int capture = PieceTypeOn(pos, moves[j].to);
		if (moves[j] == tt_move) {
			move_scores[j] = 1LL << 62;
		}
		else if (capture != PT_NB) {
			move_scores[j] = ((capture + 1) * (1LL << 54)) - PieceTypeOn(pos, moves[j].from);
		}
		else if (moves[j] == stack[ply].killer) {
			move_scores[j] = 1LL << 50;
		}
		else {
			move_scores[j] = hh_table[pos.flipped][moves[j].from][moves[j].to];
		}
	}
	int quiet_moves_evaluated = 0;
	int moves_evaluated = 0;
	int best_score = -INF;
	Move best_move{};
	uint16_t tt_flag = lowerbound;
	hash_history.emplace_back(tt_key);
	for (int i = 0; i < num_moves; ++i) {
		int best_move_index = i;
		for (int j = i; j < num_moves; ++j) {
			if (move_scores[j] > move_scores[best_move_index]) {
				best_move_index = j;
			}
		}
		const auto move = moves[best_move_index];
		const auto best_move_score = move_scores[best_move_index];
		moves[best_move_index] = moves[i];
		move_scores[best_move_index] = move_scores[i];
		auto npos = pos;
		if (!MakeMove(npos, move))
			continue;
		int score = -SearchAlpha(npos, -beta, -alpha, depth - 1, ply + 1, stack, hh_table, hash_history);
		if (info.stop) { hash_history.pop_back(); return 0; }
		if (score > best_score) {
			best_score = score;
			best_move = move;
			if (score > alpha) {
				tt_flag = exact;
				alpha = score;
				stack[ply].move = move;
				if (!ply) {
					cout << "info";
					cout << " depth " << depth;
					if (abs(score) < MATE_VALUE - MAX_DEPTH)
						cout << " score cp " << score;
					else
						cout << " score mate " << (score > 0 ? (MATE_VALUE - score + 1) >> 1 : -(MATE_VALUE + score) >> 1);
					const auto elapsed = GetTimeMs() - info.timeStart;
					cout << " alpha " << alpha;
					cout << " beta " << beta;
					cout << " time " << elapsed;
					cout << " nodes " << info.nodes;
					cout << " hashfull " << Permill();
					cout << " pv";
					PrintPv(pos, stack[0].move, hash_history);
					cout << endl;
				}
			}
		}
		if (alpha >= beta) {
			tt_flag = upperbound;
			const int capture = PieceTypeOn(pos, move.to);
			if (capture == PT_NB) {
				hh_table[pos.flipped][move.from][move.to] += depth * depth;
				stack[ply].killer = move;
			}
			break;
		}
	}
	hash_history.pop_back();
	if (best_score == -INF) {
		return in_qsearch ? alpha : in_check ? ply - MATE_VALUE : 0;
	}
	if (tt_entry.key != tt_key || depth >= tt_entry.depth || tt_flag == 0) {
		tt_entry =
			TT_Entry{ tt_key, best_move == no_move ? tt_move : best_move, best_score, in_qsearch ? 0 : depth, tt_flag };
	}
	return alpha;
}

static Move SearchIteratively(Position& pos, vector<U64>& hash_history) {
	info.stop = false;
	info.nodes = 0;
	info.timeStart = GetTimeMs();
	TranspositionClear();
	for (int depth = 1; depth <= info.depthLimit; ++depth) {
		SearchAlpha(pos, -MATE_VALUE, MATE_VALUE, depth, 0, stack, hh_table, hash_history);
		if (info.stop)
			break;
		if (info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit / 2) {
			break;
		}
	}
	return stack[0].move;
}

static void SetFen(Position& pos, const string& fen) {
	pos.flipped = false;
	pos.score = 0;
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
			pos.score += materialValOrg[piece] * (side ? -1 : 1);
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
	if (black_move)
		FlipPosition(pos);
}

static void PrintBoard(Position& pos) {
	Position np = pos;
	if (np.flipped)
		FlipPosition(np);
	const char* s = "   +---+---+---+---+---+---+---+---+\n";
	const char* t = "     A   B   C   D   E   F   G   H\n";
	cout << t;
	for (int i = 56; i >= 0; i -= 8) {
		cout << s << " " << i / 8 + 1 << " ";
		for (int j = 0; j < 8; j++) {
			int sq = i + j;
			int piece = PieceTypeOn(np, sq);
			if (np.color[0] & 1ull << sq)
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
		if (!np.castling[n])
			castling[n] = '-';
	printf("side     : %10s\n", pos.flipped ? "black" : "white");
	printf("castling : %10s\n", castling);
}

static void ParsePosition(string command) {
	string fen = DEFAULT_FEN;
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
	while (ss >> token) {
		Move m = UciToMove(token, pos.flipped);
		MakeMove(pos, m);
	}
}

static void ParseGo(string command) {
	std::stringstream ss(command);
	std::string token;
	ss >> token;
	if (token != "go")
		return;
	info.stop = false;
	info.nodes = 0;
	info.depthLimit = 64;
	info.nodesLimit = 0;
	info.timeLimit = 0;
	info.timeStart = GetTimeMs();
	int wtime = 0;
	int btime = 0;
	int winc = 0;
	int binc = 0;
	int movestogo = 32;
	char* argument = NULL;
	while (ss >> token) {
		if (token == "wtime") {
			ss >> wtime;
		}
		else if (token == "btime") {
			ss >> btime;
		}
		else if (token == "winc") {
			ss >> winc;
		}
		else if (token == "binc") {
			ss >> binc;
		}
		else if (token == "movestogo") {
			ss >> movestogo;
		}
		else if (token == "movetime") {
			ss >> info.timeLimit;
		}
		else if (token == "depth") {
			ss >> info.depthLimit;
		}
		else if (token == "nodes") {
			ss >> info.nodesLimit;
		}
	}
	int time = pos.flipped ? btime : wtime;
	int inc = pos.flipped ? binc : winc;
	if (time)
		info.timeLimit = min(time / movestogo + inc, time / 2);
}

static void UciCommand(string command) {
	if (command.empty())
		return;
	if (command == "uci")
	{
		cout << "id name " << NAME << endl;
		cout << "uciok" << endl;
	}
	else if (command == "isready")
		cout << "readyok" << endl;
	else if (command.substr(0, 8) == "position") {
		pos = Position();
		hash_history.clear();
		ParsePosition(command);
	}
	else if (command.substr(0, 2) == "go") {
		ParseGo(command);
		const Move best_move = SearchIteratively(pos, hash_history);
		cout << "bestmove " << MoveToUci(best_move, pos.flipped) << endl << flush;
	}
	else if (command == "print") {
		PrintBoard(pos);
	}
	else if (command == "quit")
		exit(0);
}

static void UciLoop() {
	//UciCommand("position startpos moves b1c3 g7g6 d2d4 f8g7 c1e3");
	//UciCommand("go depth 5");
	string line;
	while (true) {
		getline(cin, line);
		UciCommand(line);
	}
}

int main(const int argc, const char** argv) {
	cout << NAME << " " << VERSION << endl;
	SetFen(pos, DEFAULT_FEN);
	for (auto& key : keys)
		key = RAND_64;
	UciLoop();
}
