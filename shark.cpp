#include <iostream>
#include <sstream> 
#include <random>
#include <string>
#include <immintrin.h>

#if defined(_WIN32) || defined(_WIN64)
#include <windows.h>
#endif

using namespace std;

#define INF 32001
#define MATE 32000
#define MAX_PLY 64
#define U8 unsigned __int8
#define S16 signed __int16
#define U16 unsigned __int16
#define S32 signed __int32
#define S64 signed __int64
#define U64 unsigned __int64
#define NAME "Shark"
#define VERSION "2026-08-01"
#define START_FEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
#define FLIP(sq) ((sq)^0b111000)

enum Color { WHITE, BLACK, COLOR_NB };
enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };
enum Bound { LOWER, UPPER, EXACT };
enum Phase { MG, EG, PHASE_NB };

enum Square : int {
	SQ_A1, SQ_B1, SQ_C1, SQ_D1, SQ_E1, SQ_F1, SQ_G1, SQ_H1,
	SQ_A2, SQ_B2, SQ_C2, SQ_D2, SQ_E2, SQ_F2, SQ_G2, SQ_H2,
	SQ_A3, SQ_B3, SQ_C3, SQ_D3, SQ_E3, SQ_F3, SQ_G3, SQ_H3,
	SQ_A4, SQ_B4, SQ_C4, SQ_D4, SQ_E4, SQ_F4, SQ_G4, SQ_H4,
	SQ_A5, SQ_B5, SQ_C5, SQ_D5, SQ_E5, SQ_F5, SQ_G5, SQ_H5,
	SQ_A6, SQ_B6, SQ_C6, SQ_D6, SQ_E6, SQ_F6, SQ_G6, SQ_H6,
	SQ_A7, SQ_B7, SQ_C7, SQ_D7, SQ_E7, SQ_F7, SQ_G7, SQ_H7,
	SQ_A8, SQ_B8, SQ_C8, SQ_D8, SQ_E8, SQ_F8, SQ_G8, SQ_H8,
	SQUARE_NB
};

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

static const U64 FILE_N_A = ~FileABB;
static const U64 FILE_N_H = ~FileHBB;

U64 filesBB[8] = { FileABB,FileBBB,FileCBB,FileDBB,FileEBB,FileFBB,FileGBB,FileHBB };
U64 ranksBB[8] = { Rank1BB,Rank2BB,Rank3BB,Rank4BB,Rank5BB,Rank6BB,Rank7BB,Rank8BB };

enum File : int { FILE_A, FILE_B, FILE_C, FILE_D, FILE_E, FILE_F, FILE_G, FILE_H, FILE_NB };
enum Rank : int { RANK_1, RANK_2, RANK_3, RANK_4, RANK_5, RANK_6, RANK_7, RANK_8, RANK_NB };

struct Position {
	bool flipped;
	int move50;
	U8 castling[4];
	U64 color[2];
	U64 pieces[6];
	U64 ep;
};

struct Move {
	U8 from;
	U8 to;
	U8 promo;
};

struct Stack {
	Move move;
	Move killer1;
	Move killer2;
	S32 score;
};

struct TTEntry {
	U64 hash;
	Move move;
	U8 flag;
	S16 score;
	S16 depth;
};

struct SSearchInfo {
	bool post;
	bool stop;
	int depthLimit;
	S64 timeStart;
	S64 timeLimit;
	U64 nodes;
	U64 nodesLimit;
}info;

struct SOptions {
	int elo = 2500;
	int eloMin = 0;
	int eloMax = 2500;
	int ttMb = 64;
}options;

const Move no_move{};
int phase = 0;
const int phaseVal[PT_NB] = { 0, 1, 1, 2, 4, 0 };
const int insufVal[PT_NB] = { 5, 2, 3, 5, 5, 0 };
int mg_material[7] = { 82, 337, 365, 477, 1025, 0 };
int eg_material[7] = { 94, 281, 297, 512,  936, 0 };
int mx_material[7] = { 94, 337, 365, 512, 1025, 0 };
int material[7] = {};

U64 ttCount = 0;
vector<TTEntry> tt;
U64 keys[848];
Stack stack[128]{};
int historyCount = 0;
U64 historyHash[1024]{};
int hh[2][64][64];
int mg_pst[PT_NB][64];
int eg_pst[PT_NB][64];
U64 bbSquare[64];
U64 bbKnightAttack[64];
U64 bbKingAttack[64];

U64 bishop_table[64][512];
U64 rook_table[64][4096];
U64 bishop_masks[64];
U64 rook_masks[64];
const int rook_deltas[4] = { 8, -8, 1, -1 };
const int bishop_deltas[4] = { 9, -9, 7, -7 };

int mg_pawn_table[64] = {
	  0,   0,   0,   0,   0,   0,  0,   0,
	 98, 134,  61,  95,  68, 126, 34, -11,
	 -6,   7,  26,  31,  65,  56, 25, -20,
	-14,  13,   6,  21,  23,  12, 17, -23,
	-27,  -2,  -5,  12,  17,   6, 10, -25,
	-26,  -4,  -4, -10,   3,   3, 33, -12,
	-35,  -1, -20, -23, -15,  24, 38, -22,
	  0,   0,   0,   0,   0,   0,  0,   0,
};

int eg_pawn_table[64] = {
	  0,   0,   0,   0,   0,   0,   0,   0,
	178, 173, 158, 134, 147, 132, 165, 187,
	 94, 100,  85,  67,  56,  53,  82,  84,
	 32,  24,  13,   5,  -2,   4,  17,  17,
	 13,   9,  -3,  -7,  -7,  -8,   3,  -1,
	  4,   7,  -6,   1,   0,  -5,  -1,  -8,
	 13,   8,   8,  10,  13,   0,   2,  -7,
	  0,   0,   0,   0,   0,   0,   0,   0,
};

int mg_knight_table[64] = {
	-167, -89, -34, -49,  61, -97, -15, -107,
	 -73, -41,  72,  36,  23,  62,   7,  -17,
	 -47,  60,  37,  65,  84, 129,  73,   44,
	  -9,  17,  19,  53,  37,  69,  18,   22,
	 -13,   4,  16,  13,  28,  19,  21,   -8,
	 -23,  -9,  12,  10,  19,  17,  25,  -16,
	 -29, -53, -12,  -3,  -1,  18, -14,  -19,
	-105, -21, -58, -33, -17, -28, -19,  -23,
};

int eg_knight_table[64] = {
	-58, -38, -13, -28, -31, -27, -63, -99,
	-25,  -8, -25,  -2,  -9, -25, -24, -52,
	-24, -20,  10,   9,  -1,  -9, -19, -41,
	-17,   3,  22,  22,  22,  11,   8, -18,
	-18,  -6,  16,  25,  16,  17,   4, -18,
	-23,  -3,  -1,  15,  10,  -3, -20, -22,
	-42, -20, -10,  -5,  -2, -20, -23, -44,
	-29, -51, -23, -15, -22, -18, -50, -64,
};

int mg_bishop_table[64] = {
	-29,   4, -82, -37, -25, -42,   7,  -8,
	-26,  16, -18, -13,  30,  59,  18, -47,
	-16,  37,  43,  40,  35,  50,  37,  -2,
	 -4,   5,  19,  50,  37,  37,   7,  -2,
	 -6,  13,  13,  26,  34,  12,  10,   4,
	  0,  15,  15,  15,  14,  27,  18,  10,
	  4,  15,  16,   0,   7,  21,  33,   1,
	-33,  -3, -14, -21, -13, -12, -39, -21,
};

int eg_bishop_table[64] = {
	-14, -21, -11,  -8, -7,  -9, -17, -24,
	 -8,  -4,   7, -12, -3, -13,  -4, -14,
	  2,  -8,   0,  -1, -2,   6,   0,   4,
	 -3,   9,  12,   9, 14,  10,   3,   2,
	 -6,   3,  13,  19,  7,  10,  -3,  -9,
	-12,  -3,   8,  10, 13,   3,  -7, -15,
	-14, -18,  -7,  -1,  4,  -9, -15, -27,
	-23,  -9, -23,  -5, -9, -16,  -5, -17,
};

int mg_rook_table[64] = {
	 32,  42,  32,  51, 63,  9,  31,  43,
	 27,  32,  58,  62, 80, 67,  26,  44,
	 -5,  19,  26,  36, 17, 45,  61,  16,
	-24, -11,   7,  26, 24, 35,  -8, -20,
	-36, -26, -12,  -1,  9, -7,   6, -23,
	-45, -25, -16, -17,  3,  0,  -5, -33,
	-44, -16, -20,  -9, -1, 11,  -6, -71,
	-19, -13,   1,  17, 16,  7, -37, -26,
};

int eg_rook_table[64] = {
	13, 10, 18, 15, 12,  12,   8,   5,
	11, 13, 13, 11, -3,   3,   8,   3,
	 7,  7,  7,  5,  4,  -3,  -5,  -3,
	 4,  3, 13,  1,  2,   1,  -1,   2,
	 3,  5,  8,  4, -5,  -6,  -8, -11,
	-4,  0, -5, -1, -7, -12,  -8, -16,
	-6, -6,  0,  2, -9,  -9, -11,  -3,
	-9,  2,  3, -1, -5, -13,   4, -20,
};

int mg_queen_table[64] = {
	-28,   0,  29,  12,  59,  44,  43,  45,
	-24, -39,  -5,   1, -16,  57,  28,  54,
	-13, -17,   7,   8,  29,  56,  47,  57,
	-27, -27, -16, -16,  -1,  17,  -2,   1,
	 -9, -26,  -9, -10,  -2,  -4,   3,  -3,
	-14,   2, -11,  -2,  -5,   2,  14,   5,
	-35,  -8,  11,   2,   8,  15,  -3,   1,
	 -1, -18,  -9,  10, -15, -25, -31, -50,
};

int eg_queen_table[64] = {
	 -9,  22,  22,  27,  27,  19,  10,  20,
	-17,  20,  32,  41,  58,  25,  30,   0,
	-20,   6,   9,  49,  47,  35,  19,   9,
	  3,  22,  24,  45,  57,  40,  57,  36,
	-18,  28,  19,  47,  31,  34,  39,  23,
	-16, -27,  15,   6,   9,  17,  10,   5,
	-22, -23, -30, -16, -16, -23, -36, -32,
	-33, -28, -22, -43,  -5, -32, -20, -41,
};

int mg_king_table[64] = {
	-65,  23,  16, -15, -56, -34,   2,  13,
	 29,  -1, -20,  -7,  -8,  -4, -38, -29,
	 -9,  24,   2, -16, -20,   6,  22, -22,
	-17, -20, -12, -27, -30, -25, -14, -36,
	-49,  -1, -27, -39, -46, -44, -33, -51,
	-14, -14, -22, -46, -44, -30, -15, -27,
	  1,   7,  -8, -64, -43, -16,   9,   8,
	-15,  36,  12, -54,   8, -28,  24,  14,
};

int eg_king_table[64] = {
	-74, -35, -18, -18, -11,  15,   4, -17,
	-12,  17,  14,  17,  17,  38,  23,  11,
	 10,  17,  23,  15,  20,  45,  44,  13,
	 -8,  22,  24,  27,  26,  33,  26,   3,
	-18,  -4,  21,  24,  27,  23,   9, -11,
	-19,  -3,  11,  21,  23,  16,   7,  -9,
	-27, -11,   4,  13,  14,   4,  -5, -17,
	-53, -34, -21, -11, -28, -14, -24, -43
};

int* mg_table[6] = {
	mg_pawn_table,
	mg_knight_table,
	mg_bishop_table,
	mg_rook_table,
	mg_queen_table,
	mg_king_table
};

int* eg_table[6] = {
	eg_pawn_table,
	eg_knight_table,
	eg_bishop_table,
	eg_rook_table,
	eg_queen_table,
	eg_king_table
};

static bool operator==(const Move& lhs, const Move& rhs) { return !memcmp(&rhs, &lhs, sizeof(Move)); }

static inline void TTClear() { memset(tt.data(), 0, sizeof(TTEntry) * tt.size()); }
static inline void HHClear() { memset(hh, 0, sizeof(hh)); }
static inline void SSClear() { memset(stack, 0, sizeof(stack)); }
static inline U64 GetTimeMs() { return GetTickCount64(); }
static inline U64 Flip(const U64 bb) { return _byteswap_uint64(bb); }
static inline int RankOf(int sq) { return sq >> 3; }
static inline int FileOf(int sq) { return sq & 0b111; }
static inline Square LSB(const U64 bb) { return (Square)_tzcnt_u64(bb); }
static inline U64 Count(const U64 bb) { return _mm_popcnt_u64(bb); }
static inline int S(const int mg, const int eg) {return (eg << 16) + mg;}
static inline int Mg(int score) { return (short)score; }
static inline int Eg(int score) { return (score + 0x8000) >> 16; }
static inline U64 East(const U64 bb) { return (bb << 1) & FILE_N_A; }
static inline U64 West(const U64 bb) { return (bb >> 1) & FILE_N_H; }
static inline U64 North(const U64 bb) { return bb << 8; }
static inline U64 South(const U64 bb) { return bb >> 8; }
static inline U64 NW(const U64 bb) { return (bb << 7) & FILE_N_H; }
static inline U64 NE(const U64 bb) { return (bb << 9) & FILE_N_A; }
static inline U64 SW(const U64 bb) { return (bb >> 9) & FILE_N_H; }
static inline U64 SE(const U64 bb) { return (bb >> 7) & FILE_N_A; }

static void InitTT(U64 mb) {
	ttCount = (mb * 1000000) / sizeof(TTEntry);
	tt.resize(ttCount);
	TTClear();
}

static bool IsRepetition(Position& pos, U64 hash) {
	int limit = max(0, historyCount - pos.move50);
	for (int n = historyCount - 4; n >= limit; n -= 2)
		if (historyHash[n] == hash)
			return true;
	return false;
}

inline static S64 SqToBb(int sq) {
	if (sq < 0 || sq > 63)
		return 0;
	return 1ULL << sq;
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

static string SquareToUci(const int sq, const bool flip) {
	string str;
	str += 'a' + (sq % 8);
	str += '1' + (flip ? (7 - sq / 8) : (sq / 8));
	return str;
}

static auto MoveToUci(const Move& move, const bool flip) {
	string str = SquareToUci(move.from, flip);
	str += SquareToUci(move.to, flip);
	if (move.promo != PT_NB) {
		str += "\0nbrq\0\0"[move.promo];
	}
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

static int PieceTypeOnSquare(const Position& pos, const int sq) {
	const U64 bb = 1ULL << sq;
	for (int i = 0; i < 6; ++i)
		if (pos.pieces[i] & bb)
			return i;
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

inline static U64 BishopAttack(int square, U64 occupancy) {
	U64 mask = bishop_masks[square];
	return bishop_table[square][_pext_u64(occupancy, mask)];
}

inline static U64 RookAttack(int square, U64 occupancy) {
	U64 mask = rook_masks[square];
	return rook_table[square][_pext_u64(occupancy, mask)];
}

static U64 KnightAttackBB(const U64 bb) {
	return (((bb << 15) | (bb >> 17)) & 0x7F7F7F7F7F7F7F7FULL) | (((bb << 17) | (bb >> 15)) & 0xFEFEFEFEFEFEFEFEULL) |
		(((bb << 10) | (bb >> 6)) & 0xFCFCFCFCFCFCFCFCULL) | (((bb << 6) | (bb >> 10)) & 0x3F3F3F3F3F3F3F3FULL);
}

static U64 KnightAttack(const int sq, U64) {
	return bbKnightAttack[sq];
}

static U64 BishopAttackBB(U64 bb, U64 blockers) {
	return Ray(bb, blockers, NW) | Ray(bb, blockers, NE) | Ray(bb, blockers, SW) | Ray(bb, blockers, SE);
}

static U64 RookAttackBB(U64 bb, U64 blockers) {
	return Ray(bb, blockers, North) | Ray(bb, blockers, East) | Ray(bb, blockers, South) | Ray(bb, blockers, West);
}

static U64 KingAttackBB(const U64 bb) {
	return (bb << 8) | (bb >> 8) | (((bb >> 1) | (bb >> 9) | (bb << 7)) & 0x7F7F7F7F7F7F7F7FULL) |
		(((bb << 1) | (bb << 9) | (bb >> 7)) & 0xFEFEFEFEFEFEFEFEULL);
}

static U64 KingAttack(const int sq, U64) {
	return bbKingAttack[sq];
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

static auto MakeMove(Position& pos, const Move& move) {
	const int piece = PieceTypeOnSquare(pos, move.from);
	const int captured = PieceTypeOnSquare(pos, move.to);
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

static void add_move(Move* const movelist, int& num_moves, const U8 from, const U8 to, const U8 promo = PT_NB) {
	movelist[num_moves++] = Move{ from, to, promo };
}

static void generate_pawn_moves(Move* const movelist, int& num_moves, U64 to_mask, const int offset) {
	while (to_mask) {
		const int to = (int)LSB(to_mask);
		to_mask &= to_mask - 1;
		if (to >= 56) {
			add_move(movelist, num_moves, to + offset, to, KNIGHT);
			add_move(movelist, num_moves, to + offset, to, BISHOP);
			add_move(movelist, num_moves, to + offset, to, ROOK);
			add_move(movelist, num_moves, to + offset, to, QUEEN);
		}
		else
			add_move(movelist, num_moves, to + offset, to);
	}
}

static void generate_piece_moves(Move* const movelist, int& num_moves, const Position& pos, const int piece, const U64 to_mask, U64(*func)(int, U64)) {
	U64 copy = pos.color[0] & pos.pieces[piece];
	while (copy) {
		const int fr = LSB(copy);
		copy &= copy - 1;
		U64 moves = func(fr, pos.color[0] | pos.color[1]) & to_mask;
		while (moves) {
			const int to = LSB(moves);
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
	generate_pawn_moves(movelist, num_moves, North(pawns) & ~all & (only_captures ? 0xFF00000000000000ULL : 0xFFFFFFFFFFFF0000ULL), -8);
	if (!only_captures)
		generate_pawn_moves(movelist, num_moves, North(North(pawns & 0xFF00ULL) & ~all) & ~all, -16);
	generate_pawn_moves(movelist, num_moves, NW(pawns) & (pos.color[1] | pos.ep), -7);
	generate_pawn_moves(movelist, num_moves, NE(pawns) & (pos.color[1] | pos.ep), -9);
	generate_piece_moves(movelist, num_moves, pos, KNIGHT, to_mask, KnightAttack);
	generate_piece_moves(movelist, num_moves, pos, BISHOP, to_mask, BishopAttack);
	generate_piece_moves(movelist, num_moves, pos, QUEEN, to_mask, BishopAttack);
	generate_piece_moves(movelist, num_moves, pos, ROOK, to_mask, RookAttack);
	generate_piece_moves(movelist, num_moves, pos, QUEEN, to_mask, RookAttack);
	generate_piece_moves(movelist, num_moves, pos, KING, to_mask, KingAttack);
	if (!only_captures && pos.castling[0] && !(all & 0x60ULL) && !IsAttacked(pos, 4) && !IsAttacked(pos, 5)) {
		add_move(movelist, num_moves, 4, 6);
	}
	if (!only_captures && pos.castling[1] && !(all & 0xEULL) && !IsAttacked(pos, 4) && !IsAttacked(pos, 3)) {
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

static U64 GetHash(const Position& pos) {
	U64 hash = pos.flipped;
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
			hash ^= keys[6 * 64 + p * 64 + sq];
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

static bool CheckUp() {
	if ((++info.nodes & 0xffff) == 0) {
		if (info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit)
			info.stop = true;
		if (info.nodesLimit && info.nodes > info.nodesLimit)
			info.stop = true;
		if (InputAvailable()) {
			string line;
			getline(cin, line);
			if (line == "stop")
				info.stop = true;
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
	const TTEntry& ttEntry = tt[tt_key % ttCount];
	if (ttEntry.hash != tt_key || IsRepetition(npos, tt_key))
		return;
	historyHash[historyCount++] = tt_key;
	PrintPv(npos, ttEntry.move);
	historyCount--;
}

static int Popcount(const U64 bb) {
	return (int)__popcnt64(bb);
}

static int Permill() {
	int pm = 0;
	for (int n = 0; n < 1000; n++) {
		if (tt[n].hash)
			pm++;
	}
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

//prints the board
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
			int piece = PieceTypeOnSquare(np, sq);
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
	printf("side     : %16s\n", pos.flipped ? "black" : "white");
	printf("castling : %16s\n", castling);
	printf("hash     : %16llx\n", GetHash(pos));
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
	if (time < 1)
		time = 1;
	U64 nps = (nodes * 1000) / time;
	const char* units[] = { "", "k", "m", "g" };
	int sn = ShrinkNumber(nps);
	U64 p = (U64)pow(10, sn * 3);
	printf("-----------------------------\n");
	printf("Time        : %llu\n", time);
	printf("Nodes       : %llu\n", nodes);
	printf("Nps         : %llu (%llu%s/s)\n", nps, nps / p, units[sn]);
	printf("-----------------------------\n");
}

static int EvalPosition(Position& pos) {
	int phase = 0;
	int score = 0;
	int scoreMg = 0;
	int scoreEg = 0;
	int insufficient[2]{};
	U64 bbBlockers = pos.color[0] | pos.color[1];
	for (int c = WHITE; c < COLOR_NB; ++c) {
		for (int pt = PAWN; pt < KING; ++pt) {
			U64 copy = pos.color[0] & pos.pieces[pt];
			while (copy) {
				const int fr = (int)LSB(copy);
				copy &= copy - 1;
				scoreMg += mg_pst[pt][fr];
				scoreEg += eg_pst[pt][fr];
				phase += phaseVal[pt];
				insufficient[c] += insufVal[pt];
			}
		}
		U64 bbStart1 = pos.color[1] & pos.pieces[PAWN];
		U64 bbControl1 = SW(bbStart1) | SE(bbStart1);
		score -= Count(bbControl1);
		U64 bbStart0 = pos.color[0] & pos.pieces[KNIGHT];
		U64 bbAttack0 = KnightAttackBB(bbStart0) & ~bbControl1;
		score += Count(bbAttack0);
		bbStart0 = pos.color[0] & (pos.pieces[BISHOP] | pos.pieces[QUEEN]);
		bbAttack0 = BishopAttackBB(bbStart0, bbBlockers) & ~bbControl1;
		score += Count(bbAttack0);
		bbStart0 = pos.color[0] & (pos.pieces[ROOK] | pos.pieces[QUEEN]);
		bbAttack0 = RookAttackBB(bbStart0, bbBlockers) & ~bbControl1;
		score += Count(bbAttack0);
		bbStart0 = pos.color[0] & pos.pieces[KING];
		U64 file0 = filesBB[FileOf(LSB(bbStart0))];
		file0 |= East(file0) | West(file0);
		bbAttack0 = file0 & (ranksBB[1] | ranksBB[2]) & ~(FILE_D | FILE_E);
		bbAttack0 &= (pos.color[0] & pos.pieces[PAWN]);
		score += Count(bbAttack0);
		score += Count(bbAttack0 & ranksBB[1]);
		FlipPosition(pos);
		score = -score;
		scoreMg = -scoreMg;
		scoreEg = -scoreEg;
	}
	if (max(insufficient[0], insufficient[1]) < 5)return 0;
	if (insufficient[score < 0] < 4)return 0;
	if (phase > 24) phase = 24;
	score += (scoreMg * phase + scoreEg * (24 - phase)) / 24;
	return (100 - pos.move50) * score / 100;
}

static int EvalPosition4(Position& pos) {
	int mg = 0;
	int eg = 0;
	int phase = 0;
	int insufficient[2] = { 0 };
	int phases[2] = { 0 };
	U64 bbControl[2][4] = { 0 };
	U64 bbBlockers = pos.color[0] | pos.color[1];
	for (int c = WHITE; c < COLOR_NB; c++) {
		for (int pt = PAWN; pt < KING; ++pt) {
			U64 copy = pos.color[0] & pos.pieces[pt];
			while (copy) {
				const int fr = (int)LSB(copy);
				copy &= copy - 1;
				mg += mg_pst[pt][fr];
				eg += eg_pst[pt][fr];
				insufficient[c] += insufVal[pt];
				phase += phaseVal[pt];
			}
		}
		U64 bbStart0 = pos.color[0] & pos.pieces[KING];
		int sqKing = (int)LSB(bbStart0);
		U64 file0 = filesBB[FileOf(sqKing)];
		file0 |= East(file0) | West(file0);
		U64 bbAttack0 = file0 & (ranksBB[RANK_2] | ranksBB[RANK_3]) & ~(FileDBB | FileEBB);
		bbAttack0 &= (pos.color[0] & pos.pieces[PAWN]);
		mg += Count(bbAttack0);
		mg += Count(bbAttack0 & ranksBB[RANK_2]);
		FlipPosition(pos);
		mg = -mg;
		eg = -eg;
	}
	bbControl[WHITE][0] = NW(pos.color[WHITE] & pos.pieces[PAWN]) | NE(pos.color[WHITE] & pos.pieces[PAWN]);
	bbControl[BLACK][0] = SW(pos.color[BLACK] & pos.pieces[PAWN]) | SE(pos.color[BLACK] & pos.pieces[PAWN]);
	for (int c = WHITE; c < COLOR_NB; c++) {
		bbControl[c][1] = KnightAttackBB(pos.color[c] & pos.pieces[KNIGHT]);
		bbControl[c][1] |= BishopAttackBB(pos.color[c] & pos.pieces[BISHOP], bbBlockers);
		bbControl[c][2] = RookAttackBB(pos.color[c] & pos.pieces[ROOK], bbBlockers);
		bbControl[c][3] = BishopAttackBB(pos.color[c] & pos.pieces[QUEEN], bbBlockers);
		bbControl[c][3] |= RookAttackBB(pos.color[c] & pos.pieces[QUEEN], bbBlockers);
	}
	U64 bbControlW = bbControl[WHITE][0];
	U64 bbControlB = bbControl[BLACK][0];
	bbControlW |= (bbControl[WHITE][1] & ~bbControl[BLACK][0]);
	bbControlB |= (bbControl[BLACK][1] & ~bbControl[WHITE][0]);
	bbControlW |= (bbControl[WHITE][2] & ~bbControl[BLACK][1] & ~bbControl[BLACK][0]);
	bbControlB |= (bbControl[BLACK][2] & ~bbControl[WHITE][1] & ~bbControl[WHITE][0]);
	bbControlW |= (bbControl[WHITE][3] & ~bbControl[BLACK][2] & ~bbControl[BLACK][1] & ~bbControl[BLACK][0]);
	bbControlB |= (bbControl[BLACK][3] & ~bbControl[WHITE][2] & ~bbControl[WHITE][1] & ~bbControl[WHITE][0]);
	int score = Count(bbControlW) - Count(bbControlB);
	phase = min(24, phase);
	score += (mg * phase + eg * (24 - phase)) / 24;
	if (max(insufficient[0], insufficient[1]) < 5)
		return 0;
	if (insufficient[score < 0] < 4)
		return 0;
	return (100 - pos.move50) * score / 100;
}

static string StrToLower(string s) {
	transform(s.begin(), s.end(), s.begin(), ::tolower);
	return s;
}

static void SplitStr(const std::string& txt, std::vector<std::string>& vStr, char ch) {
	vStr.clear();
	if (txt == "")
		return;
	size_t pos = txt.find(ch);
	size_t initialPos = 0;
	while (pos != std::string::npos) {
		vStr.push_back(txt.substr(initialPos, pos - initialPos));
		initialPos = pos + 1;
		pos = txt.find(ch, initialPos);
	}
	vStr.push_back(txt.substr(initialPos, min(pos, txt.size()) - initialPos + 1));
}

static void SplitInt(const string& txt, vector<int>& vInt, char ch) {
	vInt.clear();
	vector<string> vs;
	SplitStr(txt, vs, ch);
	for (string s : vs)
		vInt.push_back(stoi(s));
}

static int GetVal(vector<int> v, int i) {
	if (i >= 0 && i < v.size())
		return v[i];
	return 0;
}

static void InitBitboards() {
	for (int sq = 0; sq < 64; ++sq) {
		U64 bb = 1ULL << sq;
		bbSquare[sq] = bb;
		bbKnightAttack[sq] = KnightAttackBB(bb);
		bbKingAttack[sq] = KingAttackBB(bb);
	}
}

static void InitEval() {
	vector<int> split{};
	int elo = options.elo;
	if (elo < options.eloMin)
		elo = options.eloMin;
	if (elo > options.eloMax)
		elo = options.eloMax;
	elo -= options.eloMin;
	int eloRange = options.eloMax - options.eloMin;
	int eloMod = mx_material[ROOK] * 2;
	eloMod -= (eloMod * elo) / eloRange;
	for (int pt = PAWN; pt < PT_NB; pt++) {
		int mg = mg_material[pt] - eloMod;
		int eg = eg_material[pt];
		material[pt] = S(mg, eg);
		mx_material[pt] = max(mg, eg);
	}
}

static void InitPst() {
	for (int pt = PAWN; pt <= KING; pt++) {
		for (int sq = 0; sq < 64; sq++) {
			mg_pst[pt][sq] = Mg(material[pt]) + mg_table[pt][FLIP(sq)];
			eg_pst[pt][sq] = Eg(material[pt]) + eg_table[pt][FLIP(sq)];
		}
	}
}

static int IsValid(int square, int delta) {
	int r = square / 8;
	int c = square % 8;
	int nr = (square + delta) / 8;
	int nc = (square + delta) % 8;
	if (nr < 0 || nr > 7 || nc < 0 || nc > 7) return 0;
	if (delta == 1 || delta == -1) return r == nr;
	if (delta == 9 || delta == -9 || delta == 7 || delta == -7) {
		return (r - nr == 1 || r - nr == -1) && (c - nc == 1 || c - nc == -1);
	}
	return 1;
}

static U64 GenerateSliderAttacks(int square, U64 occupancy, int is_rook) {
	U64 attacks = 0ULL;
	const int* deltas = is_rook ? rook_deltas : bishop_deltas;
	for (int i = 0; i < 4; i++) {
		int target = square;
		while (IsValid(target, deltas[i])) {
			target += deltas[i];
			attacks |= (1ULL << target);
			if (occupancy & (1ULL << target)) break;
		}
	}
	return attacks;
}

static void InitSlidersBmi2() {
	for (int sq = 0; sq < 64; sq++) {
		U64 bishop_mask = 0ULL;
		for (int i = 0; i < 4; i++) {
			int target = sq;
			while (IsValid(target, bishop_deltas[i]) && IsValid(target + bishop_deltas[i], bishop_deltas[i])) {
				target += bishop_deltas[i];
				bishop_mask |= (1ULL << target);
			}
		}
		bishop_masks[sq] = bishop_mask;

		U64 rook_mask = 0ULL;
		for (int i = 0; i < 4; i++) {
			int target = sq;
			while (IsValid(target, rook_deltas[i]) && IsValid(target + rook_deltas[i], rook_deltas[i])) {
				target += rook_deltas[i];
				rook_mask |= (1ULL << target);
			}
		}
		rook_masks[sq] = rook_mask;

		int bishop_bits = Count(bishop_mask);
		int bishop_permutations = 1 << bishop_bits;
		for (int i = 0; i < bishop_permutations; i++) {
			U64 occupancy = _pdep_u64(i, bishop_mask);
			U64 attacks = GenerateSliderAttacks(sq, occupancy, 0);
			uint64_t index = _pext_u64(occupancy, bishop_mask);
			bishop_table[sq][index] = attacks;
		}

		int rook_bits = Count(rook_mask);
		int rook_permutations = 1 << rook_bits;
		for (int i = 0; i < rook_permutations; i++) {
			U64 occupancy = _pdep_u64(i, rook_mask);
			U64 attacks = GenerateSliderAttacks(sq, occupancy, 1);

			uint64_t index = _pext_u64(occupancy, rook_mask);
			rook_table[sq][index] = attacks;
		}
	}
}

static void PrintInfo(Position& pos, Stack* stack, int depth, int score) {
	cout << "info depth " << depth << " score ";
	if (abs(score) < MATE - MAX_PLY)
		cout << "cp " << score;
	else
		cout << "mate " << (score > 0 ? (MATE - score + 1) >> 1 : -(MATE + score) >> 1);
	cout << " time " << GetTimeMs() - info.timeStart;
	cout << " nodes " << info.nodes;
	cout << " hashfull " << Permill() << " pv";
	PrintPv(pos, stack[0].move);
	cout << endl;
}

static S16 SearchAlpha(Position& pos, int alpha, int beta, int depth, int ply, Stack* stack, bool doNull = true) {
	if (CheckUp())
		return 0;
	int  mate_value = MATE - ply;
	if (alpha < -mate_value)
		alpha = -mate_value;
	if (beta > mate_value - 1)
		beta = mate_value - 1;
	if (alpha >= beta)
		return alpha;
	const int staticEval = stack[ply].score = EvalPosition(pos);
	if (ply >= MAX_PLY)
		return staticEval;
	const bool inCheck = IsAttacked(pos, (int)LSB(pos.color[0] & pos.pieces[KING]));
	if (inCheck)
		depth = max(1, depth + 1);
	bool inQuiescence = depth < 1;
	const U64 hash = GetHash(pos);
	if (ply && !inQuiescence)
		if (pos.move50 >= 100 || IsRepetition(pos, hash))
			return 0;
	TTEntry& ttEntry = tt[hash % ttCount];
	Move ttMove = { 0 };
	bool inPv = beta - alpha > 1;
	if (ttEntry.hash == hash) {
		ttMove = ttEntry.move;
		if (!inPv && ttEntry.depth >= depth) {
			if (ttEntry.flag == EXACT)return ttEntry.score;
			if (ttEntry.flag == LOWER && ttEntry.score <= alpha)return ttEntry.score;
			if (ttEntry.flag == UPPER && ttEntry.score >= beta)return ttEntry.score;
		}
	}
	else
		depth -= depth > 3;
	if (inQuiescence && alpha < staticEval) {
		alpha = staticEval;
		if (alpha >= beta)
			return beta;
	}
	U8 tt_flag = LOWER;
	Move movesList[256];
	int qNumber = 0;
	Move qList[256];
	const int movesCount = MoveGen(pos, movesList, inQuiescence);
	S64 scoreList[256];
	for (int j = 0; j < movesCount; ++j) {
		Move m = movesList[j];
		const int ptSou = PieceTypeOnSquare(pos, m.from);
		int ptDes = m.promo == PT_NB ? PieceTypeOnSquare(pos, m.to) : m.promo;
		if (m == ttMove)
			scoreList[j] = 1LL << 62;
		else if (ptDes != PT_NB)
			scoreList[j] = ((ptDes + 1) * (1LL << 54)) - ptSou;
		else if (m == stack[ply].killer1)
			scoreList[j] = 1LL << 50;
		else if (m == stack[ply].killer2)
			scoreList[j] = 1LL << 48;
		else
			scoreList[j] = hh[pos.flipped][m.from][m.to];
	}

	if (!inQuiescence && !inPv && !inCheck && ply && beta < MATE - MAX_PLY) {
		// REVERSE FUTILITY PRUNING
		if (depth < 8 && staticEval - 70 * depth >= beta)
			return staticEval - 70 * depth;
		// NULL MOVE PRUNING
		if (depth > 2 && staticEval >= beta && doNull && (pos.color[0] & (pos.pieces[KNIGHT] | pos.pieces[BISHOP] | pos.pieces[ROOK] | pos.pieces[QUEEN]))) {
			Position npos = pos;
			FlipPosition(npos);
			npos.ep = 0x0ULL;
			int R = depth >= 7 ? 4 : 3;
			int score = -SearchAlpha(npos, -beta, -beta + 1, depth - R - 1, ply + 1, stack, false);
			if (score >= beta)
				return score;
		}
	}

	historyHash[historyCount++] = hash;
	S16 score;
	int legalMoves = 0;
	const bool improving = ply > 1 && staticEval > stack[ply - 2].score;
	for (int i = 0; i < movesCount; ++i) {
		int bstIdx = i;
		for (int j = i + 1; j < movesCount; ++j)
			if (scoreList[bstIdx] < scoreList[j])
				bstIdx = j;
		Move move = movesList[bstIdx];
		scoreList[bstIdx] = scoreList[i];
		movesList[bstIdx] = movesList[i];

		// Material gain
		const S32 gain = mx_material[move.promo] + mx_material[PieceTypeOnSquare(pos, move.to)];

		// Delta pruning
		if (inQuiescence && !inCheck && staticEval + 50 + mx_material[PieceTypeOnSquare(pos, move.to)] < alpha)
			break;

		// Forward futility pruning
		if (ply > 0 && depth < 8 && !inQuiescence && !inCheck && legalMoves && staticEval + 105 * depth + gain < alpha)break;

		Position npos = pos;
		if (!MakeMove(npos, move))
			continue;
		if (!legalMoves || depth < 4)
			score = -SearchAlpha(npos, -beta, -alpha, depth - 1, ply + 1, stack);
		else {
			int r = !inPv;
			score = -SearchAlpha(npos, -alpha - 1, -alpha, depth - 1 - r, ply + 1, stack);
			if (r && score > alpha)
				score = -SearchAlpha(npos, -alpha - 1, -alpha, depth - 1, ply + 1, stack);
			if (score > alpha && score < beta)
				score = -SearchAlpha(npos, -beta, -alpha, depth - 1, ply + 1, stack);
		}
		if (info.stop)
			break;
		legalMoves++;
		int isQuiet = move.promo == PT_NB && PieceTypeOnSquare(pos, move.to) == PT_NB && (PieceTypeOnSquare(pos, move.from) != PAWN || bbSquare[move.to] != pos.ep);
		if (isQuiet)
			qList[qNumber++] = move;
		if (alpha < score)
		{
			alpha = score;
			tt_flag = EXACT;
			stack[ply].move = move;
			if (!ply && info.post)
				PrintInfo(pos, stack, depth, score);
			if (alpha >= beta) {
				tt_flag = UPPER;
				if (isQuiet) {
					stack[ply].killer2 = stack[ply].killer1;
					stack[ply].killer1 = move;
				}
				int bonus = depth * depth;
				int h = hh[pos.flipped][move.from][move.to];
				h += (bonus - h / 1024);
				hh[pos.flipped][move.from][move.to] = h;
				for (int i = 0; i < qNumber; i++) {
					Move* m = &qList[i];
					int hm = hh[pos.flipped][m->from][m->to];
					hm -= (bonus - hm / 1024);
					hh[pos.flipped][m->from][m->to] = hm;
				}
				break;
			}
		}
		if (!inCheck && !inPv && qNumber > 1 + depth * depth >> !improving)break;
	}
	historyCount--;
	if (info.stop)
		return 0;
	if (!legalMoves && !inQuiescence)
		return inQuiescence ? alpha : inCheck ? ply - MATE : 0;
	ttEntry.hash = hash;
	ttEntry.move = stack[ply].move;
	ttEntry.depth = max(0, depth);
	ttEntry.score = alpha;
	ttEntry.flag = tt_flag;
	return alpha;
}

static void SearchIteratively(Position& pos) {
	HHClear();
	SSClear();
	TTClear();
	int score = 0;
	int alpha = -MATE;
	int beta = MATE;
	for (int depth = 1; depth <= info.depthLimit; ++depth) {
		int aspH = 16, aspL = 16;
		do {
			if (depth > 4) {
				alpha = score - aspL;
				beta = score + aspH;
			}
			score = SearchAlpha(pos, alpha, beta, depth, 0, stack);
			if (score <= alpha) {
				alpha -= aspL;
				aspL *= 2;
			}
			else if (score >= beta) {
				beta += aspH;
				aspH *= 2;
			}
			else
				break;
		} while (!info.stop);
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
	for (char c : word) {
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

void PrintPerformanceHeader() {
	printf("-----------------------------\n");
	printf("ply      time        nodes\n");
	printf("-----------------------------\n");
}

//start benchmark
static void UciBench(Position& pos) {
	ResetInfo();
	PrintPerformanceHeader();
	SetFen(pos, START_FEN);
	info.depthLimit = 0;
	info.post = false;
	S64 elapsed = 0;
	while (elapsed < 3000) {
		++info.depthLimit;
		SearchIteratively(pos);
		elapsed = GetTimeMs() - info.timeStart;
		printf("%2d. %8llu %12llu\n", info.depthLimit, elapsed, info.nodes);
	}
	PrintSummary(elapsed, info.nodes);
}

//start performance test
static void UciPerformance(Position& pos) {
	ResetInfo();
	PrintPerformanceHeader();
	int depth = 0;
	SetFen(pos, START_FEN);
	while (GetTimeMs() - info.timeStart < 3000)
	{
		PerftDriver(pos, depth++);
		printf("%2d. %8llu %12llu\n", depth, GetTimeMs() - info.timeStart, info.nodes);
	}
	PrintSummary(GetTimeMs() - info.timeStart, info.nodes);
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
	historyCount = 0;
	SetFen(pos, fen);
	while (ss >> token) {
		Move m = UciToMove(token, pos.flipped);
		if (PieceTypeOnSquare(pos, m.to) != PT_NB || PieceTypeOnSquare(pos, m.from) == PAWN)
			historyCount = 0;
		historyHash[historyCount++] = GetHash(pos);
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
		info.timeLimit = min(time / movestogo + inc, time / 2);
	SearchIteratively(pos);
}

static void UciCommand(Position& pos, string command) {
	if (command.empty())
		return;
	stringstream ss(command);
	string token;
	ss >> token;
	if (token == "uci")
	{
		cout << "id name " << NAME << endl;
		cout << "option name UCI_Elo type spin default " << options.eloMax << " min " << options.eloMin << " max " << options.eloMax << endl;
		cout << "option name hash type spin default " << options.ttMb << " min 1 max 1000" << endl;
		cout << "uciok" << endl;
	}
	else if (token == "isready")
		cout << "readyok" << endl;
	else if (token == "ucinewgame") {}
	else if (token == "position")
		ParsePosition(pos, command);
	else if (token == "go")
		ParseGo(pos, command);
	else if (token == "setoption") {
		ss >> token;
		ss >> token;
		token = StrToLower(token);
		if (token == "uci_elo") {
			ss >> token;
			ss >> options.elo;
			InitEval();
			InitPst();
		}
		else if (token == "hash") {
			ss >> token;
			ss >> options.ttMb;
			InitTT(options.ttMb);
		}
	}
	else if (token == "bench")
		UciBench(pos);
	else if (token == "perft")
		UciPerformance(pos);
	else if (token == "print")
		PrintBoard(pos);
	else if (token == "quit")
		exit(0);
}

static void UciLoop(Position& pos) {
	//UciCommand(pos,"position startpos moves g1f3 d7d5 g2g3 b8c6 f1g2 e7e5 d2d3 g8f6 c2c3 f8e7 e1g1 e8g8 b1d2 c8e6 e2e4 a8c8 d3d4 f6e4 d2e4 d5e4 f3e5 c6e5 d4e5 d8d1 f1d1 e6f5 d1e1 f8d8 a2a4 h7h6 g1f1 f7f6 e5f6 e7f6 g2e4 f5e4 e1e4 d8d1 e4e1 d1e1 f1e1 a7a5 c1f4 g8f7 e1f1 f6g5 f4e5 g5f6 e5f6 f7f6 a1d1 c8b8 d1d7 b7b5 b2b3 c7c5 d7d6 f6e5 d6d7 b5a4 b3a4 g7g5 d7a7 b8b3 a7a5 b3c3 a5a6 c3a3 f1g2 c5c4 a6h6 c4c3 h6g6 e5d4 g6d6 d4c5 d6d8 a3a4 g2f1 a4c4 d8d1 c3c2 d1c1 c5d4 f1e2 d4c3 c1c2 c3c2 h2h4 g5h4 g3h4 c4h4 f2f3 h4h1 f3f4 h1h3 f4f5 c2b3 f5f6 b3c4 f6f7 h3h8 f7f8q h8f8 e2e3 c4d5 e3d2 d5d4 d2e2 f8f7 e2d2 f7f2 d2e1 f2b2 e1d1 d4d3 d1e1 b2c2");
	//UciCommand(pos,"go depth 1");
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
	InitBitboards();
	InitHash();
	InitEval();
	InitPst();
	InitSlidersBmi2();
	InitTT(options.ttMb);
	SetFen(pos, START_FEN);
	UciLoop(pos);
}
