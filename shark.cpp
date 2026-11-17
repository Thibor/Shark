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
#define MAX_MOVE 256
#define U8 unsigned __int8
#define S16 signed __int16
#define U16 unsigned __int16
#define S32 signed __int32
#define U32 unsigned __int32
#define S64 signed __int64
#define U64 unsigned __int64
#define NAME "Shark"
#define VERSION "2026-08-01"
#define START_FEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
#define RANK_1_BB 0x00000000000000FFULL
#define RANK_2_BB 0x000000000000FF00ULL
#define RANK_3_BB 0x0000000000FF0000ULL
#define RANK_4_BB 0x00000000FF000000ULL
#define RANK_5_BB 0x000000FF00000000ULL
#define RANK_6_BB 0x0000FF0000000000ULL
#define RANK_7_BB 0x00FF000000000000ULL
#define RANK_8_BB 0xFF00000000000000ULL
#define FILE_A_BB 0x0101010101010101ULL
#define FILE_B_BB 0x0202020202020202ULL
#define FILE_C_BB 0x0404040404040404ULL
#define FILE_D_BB 0x0808080808080808ULL
#define FILE_E_BB 0x1010101010101010ULL
#define FILE_F_BB 0x2020202020202020ULL
#define FILE_G_BB 0x4040404040404040ULL
#define FILE_H_BB 0x8080808080808080ULL
#define BIT(square) (1ULL << (square))
#define COUNT(bitboard) _mm_popcnt_u64(bitboard)
#define FLIP_SQ(sq) ((sq)^0x38)
#define FLIP_BB(bitboard) _byteswap_uint64(bitboard)
#define LSB(bitboard) _tzcnt_u64(bitboard)

enum File { FILE_A, FILE_B, FILE_C, FILE_D, FILE_E, FILE_F, FILE_G, FILE_H, FILE_NB };
enum Rank { RANK_1, RANK_2, RANK_3, RANK_4, RANK_5, RANK_6, RANK_7, RANK_8, RANK_NB };
enum Color { WHITE, BLACK, COLOR_NB };
enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };
enum Bound { TT_UPPER, TT_LOWER, TT_EXACT };
enum Phase { MG, EG, PHASE_NB };
enum Castle { CASTLE_WK = 0b0001, CASTLE_WQ = 0b0010, CASTLE_BK = 0b0100, CASTLE_BQ = 0b1000 };

enum Square : int {
	SQ_A1, SQ_B1, SQ_C1, SQ_D1, SQ_E1, SQ_F1, SQ_G1, SQ_H1,
	SQ_A2, SQ_B2, SQ_C2, SQ_D2, SQ_E2, SQ_F2, SQ_G2, SQ_H2,
	SQ_A3, SQ_B3, SQ_C3, SQ_D3, SQ_E3, SQ_F3, SQ_G3, SQ_H3,
	SQ_A4, SQ_B4, SQ_C4, SQ_D4, SQ_E4, SQ_F4, SQ_G4, SQ_H4,
	SQ_A5, SQ_B5, SQ_C5, SQ_D5, SQ_E5, SQ_F5, SQ_G5, SQ_H5,
	SQ_A6, SQ_B6, SQ_C6, SQ_D6, SQ_E6, SQ_F6, SQ_G6, SQ_H6,
	SQ_A7, SQ_B7, SQ_C7, SQ_D7, SQ_E7, SQ_F7, SQ_G7, SQ_H7,
	SQ_A8, SQ_B8, SQ_C8, SQ_D8, SQ_E8, SQ_F8, SQ_G8, SQ_H8,
	SQ_NB
};

static const U64 FILE_N_A = ~FILE_A_BB;
static const U64 FILE_N_H = ~FILE_H_BB;

struct Position {
	bool flipped;
	U8 move50;
	U8 castleFlags;
	U64 color[2];
	U64 pieces[6];
	U64 ep;
}pos;

typedef union {
	U32 move;
	struct {
		U8 from;
		U8 to;
		U8 promo;
		U8 flag;
	};
}Move;

struct Stack {
	S16 score;
	Move move;
	Move killer1;
	Move killer2;
};

struct TTEntry {
	U64 hash;
	Move move;
	U8 flag;
	S16 score;
	S16 depth;
};

struct TTEntryEval {
	U64 hash;
	S16 score;
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
	string factors = "16,8,15,23,16,19";

}options;

int factors[6] = {};

const Move no_move{};
int phase = 0;
const int phaseVal[PT_NB] = { 0, 1, 1, 2, 4, 0 };
const int insufVal[PT_NB] = { 5, 2, 3, 5, 5, 0 };
const int mobility[PT_NB] = { 0, 8,13,14,27, 0 };
int mg_material[7] = { 82, 337, 365, 477, 1025, 0 };
int eg_material[7] = { 94, 281, 297, 512,  936, 0 };
int mx_material[7] = { 94, 337, 365, 512, 1025, 0 };
int material[7] = {};

U64 ttCount;
U64 ttMask;
vector<TTEntry> tt;
vector<TTEntryEval> ttEval;
U64 keys[848];
Stack ss[128]{};
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
int LINEAR_REDUCTION[64][64];
const int rook_deltas[4] = { 8, -8, 1, -1 };
const int bishop_deltas[4] = { 9, -9, 7, -7 };
U64 bbFiles[8] = { FILE_A_BB, FILE_B_BB, FILE_C_BB, FILE_D_BB, FILE_E_BB, FILE_F_BB, FILE_G_BB, FILE_H_BB };
U64 bbRanks[8] = { RANK_1_BB, RANK_2_BB, RANK_3_BB, RANK_4_BB, RANK_5_BB, RANK_6_BB, RANK_7_BB, RANK_8_BB };
int boardCastle[64] = {
	 7, 15, 15, 15,  3, 15, 15, 11,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	13, 15, 15, 15, 12, 15, 15, 14
};

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

void UciCommand(string command);

static inline void HHClear() { memset(hh, 0, sizeof(hh)); }
static inline void SSClear() { memset(ss, 0, sizeof(ss)); }
static inline void TTClear() { memset(tt.data(), 0, sizeof(TTEntry) * tt.size()); }
static inline void TTEvalClear() { memset(ttEval.data(), 0, sizeof(TTEntryEval) * ttEval.size()); }
static inline int RankOf(int sq) { return sq >> 3; }
static inline int FileOf(int sq) { return sq & 7; }
static inline int S(const int mg, const int eg) { return (eg << 16) + mg; }
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

static inline U64 GetTimeMs() {
#if defined(_WIN32)
	static LARGE_INTEGER freq;
	static int init = 0;
	if (!init) {
		QueryPerformanceFrequency(&freq);
		init = 1;
	}
	LARGE_INTEGER counter;
	QueryPerformanceCounter(&counter);
	return (U64)((counter.QuadPart * 1000) / freq.QuadPart);
#else
	struct timespec ts;
	clock_gettime(CLOCK_MONOTONIC, &ts);
	return (U64)(ts.tv_sec * 1000 + ts.tv_nsec / 1000000);
#endif
}

static int GetVal(vector<int> v, int i) {
	if (i >= 0 && i < v.size())
		return v[i];
	return 0;
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
	vector<int> vf;
	SplitInt(options.factors, vf, ',');
	for (int n = 0; n < vf.size(); n++)
		factors[n] = GetVal(vf, n);
}

static void InitTT(int mb) {
	int entrySize = sizeof(TTEntry) + sizeof(TTEntryEval);
	ttCount = 1;
	while (ttCount * entrySize < mb * 1e6)
		ttCount <<= 1;
	ttMask = ttCount - 1;
	tt.resize(ttCount);
	ttEval.resize(ttCount);
	TTClear();
	TTEvalClear();
}

static bool IsRepetition(Position& pos, U64 hash) {
	int limit = max(0, historyCount - pos.move50);
	for (int n = historyCount - 4; n >= limit; n -= 2)
		if (historyHash[n] == hash)
			return true;
	return false;
}

static void FlipPosition(Position& pos) {
	pos.color[0] = FLIP_BB(pos.color[0]);
	pos.color[1] = FLIP_BB(pos.color[1]);
	for (int i = 0; i < 6; ++i)
		pos.pieces[i] = FLIP_BB(pos.pieces[i]);
	pos.ep = FLIP_BB(pos.ep);
	swap(pos.color[0], pos.color[1]);
	pos.castleFlags = ((pos.castleFlags >> 2) | (pos.castleFlags << 2)) & 0xf;
	pos.flipped = !pos.flipped;
}

static string SquareToStr(const int sq, const bool flip) {
	string str;
	str += 'a' + FileOf(sq);
	str += '1' + (flip ? 7 - RankOf(sq) : RankOf(sq));
	return str;
}

static auto MoveToStr(const Move& move, const bool flip) {
	string str = SquareToStr(move.from, flip);
	str += SquareToStr(move.to, flip);
	if (move.promo != PT_NB) {
		str += "\0nbrq\0\0"[move.promo];
	}
	return str;
}

static Move StrToMove(string& s, int flip) {
	Move m;
	m.from = (s[0] - 'a');
	int f = (s[1] - '1');
	m.from += 8 * (flip ? 7 - f : f);
	m.to = (s[2] - 'a');
	f = (s[3] - '1');
	m.to += 8 * (flip ? 7 - f : f);
	char* c = "_nbrq";
	int i = strchr(c, tolower(s[4])) - c;
	m.promo = (i > 0) && (i < 5) ? i : PT_NB;
	return m;
}

static int PieceTypeOn(const Position& pos, const int sq) {
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
	FlipPosition(pos);
	pos.castleFlags &= boardCastle[move.from] & boardCastle[move.to];
	return !IsAttacked(pos, (int)LSB(pos.color[1] & pos.pieces[KING]), false);
}

static void AddMove(Move* const move_list, int& num_moves, const U8 from, const U8 to, const U8 promo = PT_NB) {
	Move& move = move_list[num_moves++];
	move.from = from;
	move.to = to;
	move.promo = promo;
	move.flag = 0;
}

static void GeneratePawnMoves(Move* const movelist, int& num_moves, U64 to_mask, const int offset) {
	while (to_mask) {
		const int to = (int)LSB(to_mask);
		to_mask &= to_mask - 1;
		if (to >= 56) {
			AddMove(movelist, num_moves, to + offset, to, KNIGHT);
			AddMove(movelist, num_moves, to + offset, to, BISHOP);
			AddMove(movelist, num_moves, to + offset, to, ROOK);
			AddMove(movelist, num_moves, to + offset, to, QUEEN);
		}
		else
			AddMove(movelist, num_moves, to + offset, to);
	}
}

static void GeneratePieceMoves(Move* const movelist, int& num_moves, const Position& pos, const int piece, const U64 to_mask, U64(*func)(int, U64)) {
	U64 copy = pos.color[0] & pos.pieces[piece];
	while (copy) {
		const int fr = LSB(copy);
		copy &= copy - 1;
		U64 moves = func(fr, pos.color[0] | pos.color[1]) & to_mask;
		while (moves) {
			const int to = LSB(moves);
			moves &= moves - 1;
			AddMove(movelist, num_moves, fr, to);
		}
	}
}

static int GenerateMoves(const Position& pos, Move* const movelist, const bool only_captures) {
	int num_moves = 0;
	const U64 all = pos.color[0] | pos.color[1];
	const U64 to_mask = only_captures ? pos.color[1] : ~pos.color[0];
	const U64 pawns = pos.color[0] & pos.pieces[PAWN];
	GeneratePawnMoves(movelist, num_moves, North(pawns) & ~all & (only_captures ? 0xFF00000000000000ULL : 0xFFFFFFFFFFFF0000ULL), -8);
	if (!only_captures)
		GeneratePawnMoves(movelist, num_moves, North(North(pawns & 0xFF00ULL) & ~all) & ~all, -16);
	GeneratePawnMoves(movelist, num_moves, NW(pawns) & (pos.color[1] | pos.ep), -7);
	GeneratePawnMoves(movelist, num_moves, NE(pawns) & (pos.color[1] | pos.ep), -9);
	GeneratePieceMoves(movelist, num_moves, pos, KNIGHT, to_mask, KnightAttack);
	GeneratePieceMoves(movelist, num_moves, pos, BISHOP, to_mask, BishopAttack);
	GeneratePieceMoves(movelist, num_moves, pos, QUEEN, to_mask, BishopAttack);
	GeneratePieceMoves(movelist, num_moves, pos, ROOK, to_mask, RookAttack);
	GeneratePieceMoves(movelist, num_moves, pos, QUEEN, to_mask, RookAttack);
	GeneratePieceMoves(movelist, num_moves, pos, KING, to_mask, KingAttack);
	if (!only_captures && (pos.castleFlags & CASTLE_WK) && !(all & 0x60ULL) && !IsAttacked(pos, SQ_E1) && !IsAttacked(pos, SQ_F1)) {
		AddMove(movelist, num_moves, 4, 6);
	}
	if (!only_captures && (pos.castleFlags & CASTLE_WQ) && !(all & 0xEULL) && !IsAttacked(pos, SQ_E1) && !IsAttacked(pos, SQ_D1)) {
		AddMove(movelist, num_moves, 4, 2);
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
			hash ^= keys[(6 + p) * 64 + sq];
		}
	}
	if (pos.ep)
		hash ^= keys[12 * 64 + LSB(pos.ep)];
	hash ^= keys[13 * 64 + pos.castleFlags];
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
			UciCommand(line);
		}
	}
	return info.stop;
}

static bool IsPseudolegalMove(const Position& pos, const Move& move) {
	Move moves[256];
	const int num_moves = GenerateMoves(pos, moves, false);
	for (int i = 0; i < num_moves; ++i)
		if (moves[i].move == move.move)
			return true;
	return false;
}

static void PrintPv(const Position& pos, const Move move) {
	if (!IsPseudolegalMove(pos, move))
		return;
	auto npos = pos;
	if (!MakeMove(npos, move))
		return;
	cout << " " << MoveToStr(move, pos.flipped);
	const U64 hash = GetHash(npos);
	const TTEntry& ttEntry = tt[hash & ttMask];
	if (ttEntry.hash != hash || IsRepetition(npos, hash))
		return;
	historyHash[historyCount++] = hash;
	PrintPv(npos, ttEntry.move);
	historyCount--;
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

static int EvalPosition(Position& pos) {
	int phase = 0;
	int score = 0;
	int scoreMg = 0;
	int scoreEg = 0;
	int insufficient[2]{};
	for (int c = WHITE; c < COLOR_NB; ++c) {
		U64 bbBlockers = pos.color[0] | pos.color[1];
		U64 bbStart1 = pos.color[1] & pos.pieces[PAWN];
		U64 bbControl1 = SW(bbStart1) | SE(bbStart1);
		for (int pt = PAWN; pt < PT_NB; ++pt) {
			U64 copy = pos.color[0] & pos.pieces[pt];
			while (copy) {
				const int fr = (int)LSB(copy);
				copy &= copy - 1;
				scoreMg += mg_pst[pt][fr];
				scoreEg += eg_pst[pt][fr];
				phase += phaseVal[pt];
				insufficient[c] += insufVal[pt];
				if (pt > PAWN && pt < KING) {
					U64 bbAttack = Attacks(pt, fr, bbBlockers);
					score += (COUNT(bbAttack & ~bbControl1) * factors[pt + 1]) / mobility[pt];
				}
			}
		}
		U64 bbStart0 = pos.color[0] & pos.pieces[KING];
		U64 file0 = bbFiles[FileOf(LSB(bbStart0))];
		file0 |= East(file0) | West(file0);
		U64 bbAttack0 = file0 & ~(FILE_D_BB | FILE_E_BB);
		bbAttack0 &= (pos.color[0] & pos.pieces[PAWN]);
		scoreMg += COUNT(bbAttack0 & RANK_2_BB) * factors[0];
		scoreMg += COUNT(bbAttack0 & RANK_3_BB) * factors[1];
		FlipPosition(pos);
		score = -score;
		scoreMg = -scoreMg;
		scoreEg = -scoreEg;
	}
	if (phase > 24) phase = 24;
	score += (scoreMg * phase + scoreEg * (24 - phase)) / 24;
	if (max(insufficient[0], insufficient[1]) < 5)return 0;
	if (insufficient[score < 0] < 4)return 0;
	return score;
}

static int EvalHash(Position& pos, U64 hash) {
	TTEntryEval& ee = ttEval[hash & ttMask];
	if (ee.hash != hash) {
		ee.hash = hash;
		ee.score = EvalPosition(pos);
	}
	return (ee.score * (100 - pos.move50)) / 100;
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
		if (!(np.castleFlags & (1 << n)))
			castling[n] = '-';
	printf("side     : %16s\n", pos.flipped ? "black" : "white");
	printf("castling : %16s\n", castling);
	printf("ep       : %16s\n", pos.ep ? SquareToStr((int)LSB(pos.ep), pos.flipped).c_str() : "-");
	printf("50-move  : %16d\n", pos.move50);
	printf("hash     : %16llx\n", GetHash(pos));
	printf("score    : %16d\n", EvalPosition(pos));
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

static string StrToLower(string s) {
	transform(s.begin(), s.end(), s.begin(), ::tolower);
	return s;
}

static void Init() {
	for (int depth = 1; depth < 64; depth++)
		for (int legal = 1; legal < 64; legal++)
			LINEAR_REDUCTION[depth][legal] = (int)(0.75 + log(depth) * log(legal) / 2.25);
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
			mg_pst[pt][sq] = Mg(material[pt]) + mg_table[pt][FLIP_SQ(sq)];
			eg_pst[pt][sq] = Eg(material[pt]) + eg_table[pt][FLIP_SQ(sq)];
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

		int bishop_bits = COUNT(bishop_mask);
		int bishop_permutations = 1 << bishop_bits;
		for (int i = 0; i < bishop_permutations; i++) {
			U64 occupancy = _pdep_u64(i, bishop_mask);
			U64 attacks = GenerateSliderAttacks(sq, occupancy, 0);
			uint64_t index = _pext_u64(occupancy, bishop_mask);
			bishop_table[sq][index] = attacks;
		}

		int rook_bits = COUNT(rook_mask);
		int rook_permutations = 1 << rook_bits;
		for (int i = 0; i < rook_permutations; i++) {
			U64 occupancy = _pdep_u64(i, rook_mask);
			U64 attacks = GenerateSliderAttacks(sq, occupancy, 1);

			uint64_t index = _pext_u64(occupancy, rook_mask);
			rook_table[sq][index] = attacks;
		}
	}
}

static void PrintInfo(Position& pos, int depth, int score) {
	cout << "info depth " << depth << " score ";
	if (abs(score) < MATE - MAX_PLY)
		cout << "cp " << score;
	else
		cout << "mate " << (score > 0 ? (MATE - score + 1) >> 1 : -(MATE + score) >> 1);
	cout << " time " << GetTimeMs() - info.timeStart;
	cout << " nodes " << info.nodes;
	cout << " hashfull " << Permill() << " pv";
	PrintPv(pos, ss[0].move);
	cout << endl;
}

static int ScoreToTT(int score, int ply) {
	if (score >= MATE - MAX_PLY) return score + ply;
	if (score <= -MATE + MAX_PLY) return score - ply;
	return score;
}

static int ScoreFromTT(int score, int ply) {
	if (score >= MATE - MAX_PLY) return score - ply;
	if (score <= -MATE + MAX_PLY) return score + ply;
	return score;
}

static S16 SearchAlpha(Position& pos, int alpha, int beta, int depth, int ply, bool doNull = true) {
	if (CheckUp())
		return 0;
	int  mate_value = MATE - ply;
	if (alpha < -mate_value)
		alpha = -mate_value;
	if (beta > mate_value - 1)
		beta = mate_value - 1;
	if (alpha >= beta)
		return alpha;
	const U64 hash = GetHash(pos);
	const int staticEval = ss[ply].score = EvalHash(pos, hash);
	if (ply >= MAX_PLY - 1)
		return staticEval;
	const bool inCheck = IsAttacked(pos, (int)LSB(pos.color[0] & pos.pieces[KING]));
	if (inCheck)
		depth = max(1, depth + 1);
	bool inQuiescence = depth < 1;
	if (ply && !inQuiescence) {
		if (!(pos.pieces[PAWN] | pos.pieces[ROOK] | pos.pieces[QUEEN]) && COUNT(pos.pieces[BISHOP] | pos.pieces[KNIGHT]) <2)
			return 0;
		if (pos.move50 > 99 || IsRepetition(pos, hash))
			return 0;
	}
	int ttScore = 0;
	TTEntry& ttEntry = tt[hash & ttMask];
	ss[ply +1].move.move = 0;
	Move ttMove = ss[ply+1].move;
	bool inPv = beta - alpha > 1;
	if (ttEntry.hash == hash) {
		ttMove = ttEntry.move;
		ttScore = ScoreFromTT(ttEntry.score, ply);
		if (!inPv && ttEntry.depth >= depth) {
			if (ttEntry.flag == TT_EXACT)return ttScore;
			if (ttEntry.flag == TT_UPPER && ttScore <= alpha)return ttScore;
			if (ttEntry.flag == TT_LOWER && ttScore >= beta)return ttScore;
		}
	}
	else
		depth -= depth > 3;
	if (inQuiescence && alpha < staticEval) {
		alpha = staticEval;
		if (alpha >= beta)
			return beta;
	}
	const int improving = ply > 1 && staticEval > ss[ply - 2].score;
	if (ply && !inQuiescence && !inCheck && !inPv) {

		// Reverse futility pruning
		if (depth < 8) {
			if (staticEval - 71 * (depth - improving) >= beta)
				return staticEval;
			inQuiescence = staticEval + 238 * depth < alpha;
		}

		// Null move pruning
		if (depth > 2 && staticEval >= beta && doNull && pos.color[0] & ~pos.pieces[PAWN] & ~pos.pieces[KING]) {
			Position npos = pos;
			FlipPosition(npos);
			npos.ep = 0x0ULL;
			if (-SearchAlpha(npos, -beta, -alpha, depth - 4 - depth / 5 - min((staticEval - beta) / 196, 3), ply + 1, false) >= beta)
				return beta;
		}
	}
	historyHash[historyCount++] = hash;
	U8 ttFlag = TT_UPPER;
	int legalCount = 0;
	int score;
	int quietCount = 0;
	Move movesList[MAX_MOVE];
	Move quietList[MAX_MOVE];
	S64 scoreList[MAX_MOVE];
	S32 best_score = inQuiescence ? staticEval : -INF;
	const int movesCount = GenerateMoves(pos, movesList, inQuiescence);
	for (int j = 0; j < movesCount; ++j) {
		Move m = movesList[j];
		const int ptSou = PieceTypeOn(pos, m.from);
		const int ptDes = m.promo == PT_NB ? PieceTypeOn(pos, m.to) : m.promo;
		if (m.move == ttMove.move)
			scoreList[j] = BIT(62);
		else if (ptDes != PT_NB)
			scoreList[j] = BIT(54) + ptDes * 10 - ptSou;
		else if (m.move == ss[ply].killer1.move)
			scoreList[j] = BIT(49);
		else if (m.move == ss[ply].killer2.move)
			scoreList[j] = BIT(48);
		else
			scoreList[j] = hh[pos.flipped][m.from][m.to];
	}
	for (int i = 0; i < movesCount; ++i) {
		int bstIdx = i;
		for (int j = i + 1; j < movesCount; ++j)
			if (scoreList[bstIdx] < scoreList[j])
				bstIdx = j;
		Move move = movesList[bstIdx];
		scoreList[bstIdx] = scoreList[i];
		movesList[bstIdx] = movesList[i];

		// Material gain
		const int gain = mx_material[move.promo] + mx_material[PieceTypeOn(pos, move.to)];

		// Delta pruning
		if (inQuiescence && !inCheck && staticEval + 50 + mx_material[PieceTypeOn(pos, move.to)] < alpha)
			break;

		// Forward futility pruning
		if (ply > 0 && depth < 8 && !inQuiescence && !inCheck && legalCount && staticEval + 105 * depth + gain < alpha)
			break;

		Position npos = pos;
		if (!MakeMove(npos, move))
			continue;
		if (!legalCount || inCheck || depth < 4)
			score = -SearchAlpha(npos, -beta, -alpha, depth - 1, ply + 1);
		else {
			int r = LINEAR_REDUCTION[min(63, depth)][min(63, legalCount)];
			const int givesCheck = IsAttacked(npos, LSB(npos.color[0] & npos.pieces[KING]), 1);
			if (inPv)
				r--;
			if (inCheck || givesCheck)
				r--;
			if (gain)
				r--;
			if (r > depth - 2)
				r = depth - 2;
			if (r < 0)
				r = 0;
			score = -SearchAlpha(npos, -alpha - 1, -alpha, depth - 1 - r, ply + 1);
			if (r && score > alpha)
				score = -SearchAlpha(npos, -alpha - 1, -alpha, depth - 1, ply + 1);
			if (score > alpha && score < beta)
				score = -SearchAlpha(npos, -beta, -alpha, depth - 1, ply + 1);
		}
		if (info.stop)
			break;
		legalCount++;
		if (best_score < score)best_score = score;
		if (alpha < score) {
			alpha = score;
			ttFlag = TT_EXACT;
			ss[ply].move.move = move.move;
			if (!ply && info.post)
				PrintInfo(pos, depth, score);
			if (alpha >= beta) {
				ttFlag = TT_LOWER;
				if (!gain) {
					ss[ply].killer2.move = ss[ply].killer1.move;
					ss[ply].killer1.move = move.move;
					int bonus = depth * depth;
					hh[pos.flipped][move.from][move.to] +=
						bonus - bonus * hh[pos.flipped][move.from][move.to] / 512;
					for (int j = 0; j < quietCount; ++j)
						hh[pos.flipped][quietList[j].from][quietList[j].to] -=
						bonus + bonus * hh[pos.flipped][quietList[j].from][quietList[j].to] / 512;
				}
				break;
			}
		}
		if (!gain)
			quietList[quietCount++] = move;
		if (!inCheck && !inPv && quietCount > (1 + depth * depth) >> (int)!improving)break;
	}
	historyCount--;
	if (info.stop)
		return 0;
	ttEntry.hash = hash;
	if (ss[ply].move.move)
		ttEntry.move.move = ss[ply].move.move;
	ttEntry.depth = max(0, depth);
	ttEntry.score = ScoreToTT(best_score, ply);
	ttEntry.flag = ttFlag;
	if (!legalCount && !inQuiescence)
		return inCheck ? ply - MATE : 0;
	return best_score;
}

static int SearchIteratively(Position& pos) {
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
			score = SearchAlpha(pos, alpha, beta, depth, 0);
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
		cout << "bestmove " << MoveToStr(ss[0].move, pos.flipped) << endl << flush;
	return score;
}

static inline void PerftDriver(Position pos, int depth) {
	Move list[256];
	const S32 num_moves = GenerateMoves(pos, list, false);
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
	memset(&pos, 0, sizeof(pos));
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
	for (const char c : word) {
		pos.castleFlags |= (c == 'K') ? CASTLE_WK : 0;
		pos.castleFlags |= (c == 'Q') ? CASTLE_WQ : 0;
		pos.castleFlags |= (c == 'k') ? CASTLE_BK : 0;
		pos.castleFlags |= (c == 'q') ? CASTLE_BQ : 0;
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
	printf("ply     time        nodes\n");
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
	while (elapsed < 8000) {
		++info.depthLimit;
		int score = SearchIteratively(pos);
		elapsed = GetTimeMs() - info.timeStart;
		printf("%2d. %8llu %12llu %8d", info.depthLimit, elapsed, info.nodes, score);
		PrintPv(pos, ss[0].move);
		cout << endl;
	}
	PrintSummary(elapsed, info.nodes);
}

//start performance test
static void UciPerformance(Position& pos) {
	ResetInfo();
	PrintPerformanceHeader();
	int depth = 0;
	SetFen(pos, START_FEN);
	while (GetTimeMs() - info.timeStart < 4000)
	{
		info.nodes = 0;
		info.timeStart = GetTimeMs();
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
		Move m = StrToMove(token, pos.flipped);
		historyHash[historyCount++] = GetHash(pos);
		MakeMove(pos, m);
		if (!pos.move50)
			historyCount = 0;
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

void UciCommand(string command) {
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
		cout << "option name factors type string default " << options.factors << endl;
		cout << "uciok" << endl;
	}
	else if (token == "isready")
		cout << "readyok" << endl;
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
		else if (token == "factors") {
			ss >> token;
			ss >> options.factors;
			InitFactors();
		}
	}
	else if (token == "bench")UciBench(pos);
	else if (token == "perft")UciPerformance(pos);
	else if (token == "print")PrintBoard(pos);
	else if (token == "stop")info.stop = true;
	else if (token == "quit")exit(0);
}

static void InitHash() {
	mt19937_64 r;
	for (U64& k : keys)
		k = r();
}

int main(const int argc, const char** argv) {
	Init();
	InitBitboards();
	InitHash();
	InitEval();
	InitPst();
	InitSlidersBmi2();
	InitTT(options.ttMb);
	InitFactors();
	setbuf(stdout, NULL);
	cout << NAME << " " << VERSION << endl;
	SetFen(pos, START_FEN);
	string line;
	while (true) {
		getline(cin, line);
		UciCommand(line);
	}
}
