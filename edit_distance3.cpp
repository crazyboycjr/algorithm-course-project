#include <cstdio>
#include <cstring>
#include <cassert>

#include <string>
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <iostream>

using namespace std;

enum Operation {
	NOP = 0,
	DEL,
	INS,
	SUB
};

const long maxn = 102000;
const long maxm = 1002000;
const long maxl = 32;

// encapsulation use
const long offset = maxn * maxm / 4;
int ft[maxn * maxm / 32];
class Option {
public:
	static uint8_t mem[maxn * maxm / 2];
	static bool getfa_failed(long n, long m) {
		long pos = n * maxm +  m;
		return !(ft[pos >> 5] >> (pos & 31) & 1);
	}
	static int getfa(long n, long m) {
		long pos = n * maxm + m;
		int shift = (pos & 3) << 1;
		return (mem[pos >> 2] & (3 << shift)) >> shift;
	}
	static void putfa(long n, long m, int val) {
		long pos = n * maxm + m;
		ft[pos >> 5] |= 1 << (pos & 31);
		int shift = (pos & 3) << 1;
		mem[pos >> 2] = val << shift | (~(3 << shift) & mem[pos >> 2]);
	}
	static int getopt(long n, long m) {
		long pos = n * maxm + m;
		int shift = (pos & 3) << 1;
		return (mem[(pos >> 2) + offset] & (3 << shift)) >> shift;
	}
	static void putopt(long n, long m, int val) {
		long pos = n * maxm + m;
		int shift = (pos & 3) << 1;
		mem[(pos >> 2) + offset] = val << shift | (~(3 << shift) & mem[(pos >> 2) + offset]);
	}
	static void clearopt() {
		memset(mem + offset, 0, sizeof mem / 2);
	}
};
uint8_t Option::mem[maxn * maxm / 2];


struct Edge {
	int nex, y;
} e[maxm * 4], e2[maxm * 4];
int list[maxm], cnt, list2[maxm], cnt2;
char s[maxn], out[maxn];
char ns[maxm][maxl];
//int fa[maxn][maxm];
int dp[2][maxm];
//Operation opt[maxn][maxm];
unordered_map<string, int> M[2];
unordered_map<int, vector<int>> Mv[2];
int n, k, m, tlen, outlen;
int mapping[256], rev_mapping[4];

#ifdef DEBUG
#define LOG(...) fprintf(stderr, __VA_ARGS__)
#else
#define LOG(...)
#endif

void print_opt(int n, int m) {
	if (n + m == 0)
		return;
	int tmp_opt = Option::getopt(n, m);
	switch (tmp_opt) {
		case NOP:
			print_opt(n - 1, m - 1);
			break;
		case DEL:
			print_opt(n - 1, m);
			printf("DEL %d\n", n - 1);
			break;
		case INS:
			print_opt(n, m - 1);
			printf("INS %d %c\n", n, out[m]);
			break;
		case SUB:
			print_opt(n - 1, m - 1);
			printf("SUB %d %c\n", n - 1, out[m]);
			break;
	}
}

inline int find_number(uint8_t x, int m) {
	int ret = 0, t = M[0][string(ns[m] + 1, tlen - 1)];
	for (auto v : Mv[1][t]) {
		if (ns[v][1] == x) {
			ret = v;
			break;
		}
	}
	return ret;
}

int start;
void construct(int n, int m) {
	if (n + m == 0) {
		for (int i = 1; i < tlen; i++)
			out[++outlen] = ns[start][i];
		return;
	}
	LOG("%d %d %d\n", n, m, Option::getfa(n, m));
	int fanm = rev_mapping[Option::getfa(n, m)];
	if (Option::getfa_failed(n, m)) {
		fanm = 0;
	} else {
		fanm = find_number(fanm, m);
	}
	if (Option::getfa_failed(n, m) && m != 0) {
		start = m;
	}
	int tmp_opt = Option::getopt(n, m);
	switch (tmp_opt) {
		case NOP:
			construct(n - 1, fanm);
			if (m) out[++outlen] = ns[m][tlen];
			break;
		case DEL:
			construct(n, fanm);
			if (m) out[++outlen] = ns[m][tlen];
			break;
		case INS:
			construct(n - 1, m);
			break;
		case SUB:
			construct(n - 1, fanm);
			if (m) out[++outlen] = ns[m][tlen];
			break;
	}
}

void insert(int x, int y, char *c, int len) {
	static int tot[2];
	string s = string(c, len);
	if (!M[x][s])
		M[x][s] = ++tot[x];
	if (!M[x ^ 1][s])
		M[x ^ 1][s] = ++tot[x ^ 1];
	Mv[x][M[x ^ 1][s]].push_back(y);
}

inline void addedge(int a, int b) {
	e[++cnt] = (Edge){list[a], b}; list[a] = cnt;
}

inline void addedge2(int a, int b) {
	e2[++cnt2] = (Edge){list2[a], b}; list2[a] = cnt2;
}

//int tmp_dp[2][maxn];
int tmp_dp[maxn][2];
int *calc(char *s, int n, char *t, int m, bool bf) {
	tmp_dp[0][0] = 0;

	for (int i = 1; i <= n; i++) {
		tmp_dp[i][0] = i;
		//opt[i][0] = DEL;
		Option::putopt(i, 0, DEL);
	}
	/*
	for (int i = 1; i <= m; i++) {
		tmp_dp[0][i] = i;
		opt[0][i] = INS;
	}
	*/
	static int a[maxn];
	for (int jj, j = 1; j <= m; j++) {
		jj = j & 1;
		tmp_dp[0][jj] = j;
		//opt[0][j] = INS;
		Option::putopt(0, j, INS);
		for (int i = 1; i <= n; i++) {
			if (s[i] == t[j]) {
				tmp_dp[i][jj] = tmp_dp[i - 1][jj ^ 1];
				//opt[i][j] = NOP;
				Option::putopt(i, j, NOP);
			} else {
				if (tmp_dp[i - 1][jj] < tmp_dp[i][jj ^ 1]) {
					tmp_dp[i][jj] = tmp_dp[i - 1][jj] + 1;
					//opt[i][j] = DEL;
					Option::putopt(i, j, DEL);
				} else {
					tmp_dp[i][jj] = tmp_dp[i][jj ^ 1] + 1;
					//opt[i][j] = INS;
					Option::putopt(i, j, INS);
				}
				if (tmp_dp[i][jj] > tmp_dp[i - 1][jj ^ 1] + 1) {
					tmp_dp[i][jj] = tmp_dp[i - 1][jj ^ 1] + 1;
					//opt[i][j] = SUB;
					Option::putopt(i, j, SUB);
				}
			}
		}
		if (!bf) {
			a[j] = tmp_dp[n][jj];
			if (a[j] + n == j) {
				a[j] = -1;
				break;
			}
		}
	}
	//return tmp_dp[n & 1];
	return a;
}

int main() {
	mapping['A'] = 0; mapping['G'] = 1; mapping['C'] = 2; mapping['T'] = 3;
	rev_mapping[0] = 'A'; rev_mapping[1] = 'G'; rev_mapping[2] = 'C'; rev_mapping[3] = 'T';

	fprintf(stderr, "begin to read\n");
	scanf("%s\n", s + 1);
	n = strlen(s + 1);
	scanf("%d\n", &m);
	for (int t, i = 1; i <= m; i++) {
		scanf("%s", ns[i] + 1);
		t = strlen(ns[i] + 1);
		insert(0, i, ns[i] + 1, t - 1);
		insert(1, i, ns[i] + 2, t - 1);
	}
	tlen = strlen(ns[1] + 1);

	fprintf(stderr, "begin to build graph\n");
	for (int t, i = 1; i <= m; i++) {
		t = M[1][string(ns[i] + 2)];
		//cout << t << " " << string(ns[i] + 2) << endl;
		for (auto v : Mv[0][t]) {
			addedge(v, i);
			addedge2(i, v);
			LOG("%d -> %d\n", i, v);
		}
	}
	vector<int> bound[maxm]; // XXX maybe we can use vector<uint8_t>
	fprintf(stderr, "ready to dp\n");
	memset(dp, 127, sizeof dp);
	for (int i = 1; i <= m; i++) {
		int *a = calc(ns[i], tlen, s, n, false);
		for (int j = 0; j <= n; j++) {
			//dp[j][i][1] = a[j];
			if (a[j] == -1) {
				break;
			}
			bound[i].push_back(a[j]);
			LOG("%d ", a[j]);
		}
		LOG("\n");
	}
	//memset(opt, 0, sizeof opt);
	Option::clearopt();

	static int q[2][maxm];
	static bool inq[maxm];

	for (int j = 2; j <= n; j++) {
		int jj = j & 1;
		fprintf(stderr, "current on %d\n", j);

		for (int i = 1; i <= m; i++) {
			dp[jj][i] = j >= (int)bound[i].size() ? j - tlen : bound[i][j];
		}
		int cur = 0;
		int total = m;
		int head(0), tail(0);
		for (int i = 1; i <= m; i++)
			q[cur][tail++] = i;
		do {
			for (int i = 0; i < total; i++)
				inq[q[cur][i]] = false;
			total = 0;
			while (head < tail) {
				int i = q[cur][head++];
				int &res = dp[jj][i];
				//res = j >= (int)bound[i].size() ? j - tlen : bound[i][j];
				int tmp_res = res;
				for (int y, k = list[i]; k; k = e[k].nex) {
					y = e[k].y;
					if (s[j] == ns[i][tlen]) {
						if (res > dp[jj ^ 1][y]) {
							res = dp[jj ^ 1][y];
							//fa[j][i] = ns[y][1];
							//opt[j][i] = NOP;
							Option::putfa(j, i, mapping[(int)ns[y][1]]);
							Option::putopt(j, i, NOP);
						}
					}
					if (res > dp[jj ^ 1][i] + 1) {
						res = dp[jj ^ 1][i] + 1;
						//opt[j][i] = INS;
						Option::putopt(j, i, INS);
					}
					if (res > dp[jj][y] + 1) {
						res = dp[jj][y] + 1;
						//fa[j][i] = ns[y][1];
						//opt[j][i] = DEL;
						Option::putfa(j, i, mapping[(int)ns[y][1]]);
						Option::putopt(j, i, DEL);
					}
					if (res > dp[jj ^ 1][y] + 1) {
						res = dp[jj ^ 1][y] + 1;
						//fa[j][i] = ns[y][1];
						//opt[j][i] = SUB;
						Option::putfa(j, i, mapping[(int)ns[y][1]]);
						Option::putopt(j, i, SUB);
					}
				}
				if (res < tmp_res) {
					for (int y, k = list2[i]; k; k = e2[k].nex) {
						y = e2[k].y;
						if (!inq[y]) {
							inq[y] = true;
							q[cur ^ 1][total++] = y;
						}
					}
				}
			}
			cur ^= 1;
			if (total > 0) {
				head = 0;
				tail = total;
			}
		} while (total > 0);
	}

	int ans = maxn, en;
	for (int i = 1; i <= m; i++)
		if (ans > dp[n & 1][i]) {
			ans = dp[n & 1][i];
			en = i;
		}

	LOG("%d\n", en);
	construct(n, en);

	for (int i = 1; i <= outlen; i++)
		putchar(out[i]);
	printf("\n%d\n", ans);
	
	//memset(opt, 0, sizeof opt);
	Option::clearopt();
	calc(s, n, out, outlen, true);
	print_opt(n, outlen);
	return 0;
}
