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

int pre[maxm][5], nex[maxm][5];
char s[maxn], out[maxn];
char ns[maxm][maxl];
int dp[maxm][2];
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
	pre[a][++pre[a][0]] = b;
}

inline void addedge2(int a, int b) {
	nex[a][++nex[a][0]] = b;
}

int tmp_dp[maxn][2];
int *calc(char *s, int n, char *t, int m, bool bf) {
	tmp_dp[0][0] = 0;

	for (int i = 1; i <= n; i++) {
		tmp_dp[i][0] = i;
		Option::putopt(i, 0, DEL);
	}

	static int a[maxn];
	for (int jj, j = 1; j <= m; j++) {
		jj = j & 1;
		tmp_dp[0][jj] = j;
		Option::putopt(0, j, INS);
		for (int i = 1; i <= n; i++) {
			if (s[i] == t[j]) {
				tmp_dp[i][jj] = tmp_dp[i - 1][jj ^ 1];
				Option::putopt(i, j, NOP);
			} else {
				if (tmp_dp[i - 1][jj] < tmp_dp[i][jj ^ 1]) {
					tmp_dp[i][jj] = tmp_dp[i - 1][jj] + 1;
					Option::putopt(i, j, DEL);
				} else {
					tmp_dp[i][jj] = tmp_dp[i][jj ^ 1] + 1;
					Option::putopt(i, j, INS);
				}
				if (tmp_dp[i][jj] > tmp_dp[i - 1][jj ^ 1] + 1) {
					tmp_dp[i][jj] = tmp_dp[i - 1][jj ^ 1] + 1;
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
	vector<int> bound[maxm];
	fprintf(stderr, "ready to dp\n");
	memset(dp, 127, sizeof dp);
	for (int i = 1; i <= m; i++) {
		int *a = calc(ns[i], tlen, s, n, false);
		for (int j = 0; j <= n; j++) {
			if (a[j] == -1) {
				break;
			}
			bound[i].push_back(a[j]);
			LOG("%d ", a[j]);
		}
		LOG("\n");
	}
	Option::clearopt();

	static int q[2][maxm];
	static bool inq[maxm];

	for (int j = 2; j <= n; j++) {
		int jj = j & 1, ljj = jj ^ 1;
		fprintf(stderr, "current on %d\n", j);

		for (int i = 1; i <= m; i++) {
			dp[i][jj] = j >= (int)bound[i].size() ? j - tlen : bound[i][j];
		}
		int cur = 0, total = m;
		int head(0), tail(0);
		for (int i = 1; i <= m; i++)
			q[cur][tail++] = i;
		do {
			for (int i = 0; i < total; i++)
				inq[q[cur][i]] = false;
			total = 0;
			while (head < tail) {
				int i = q[cur][head++];
				int &res = dp[i][jj];
				int tmp_res = res;
				for (int y, k = 1; k <= pre[i][0]; k++) {
					y = pre[i][k];
					if (s[j] == ns[i][tlen]) {
						if (res > dp[y][ljj]) {
							res = dp[y][ljj];
							Option::putfa(j, i, mapping[(int)ns[y][1]]);
							Option::putopt(j, i, NOP);
						}
					}
					if (res > dp[i][ljj] + 1) {
						res = dp[i][ljj] + 1;
						Option::putopt(j, i, INS);
					}
					if (res > dp[y][jj] + 1) {
						res = dp[y][jj] + 1;
						Option::putfa(j, i, mapping[(int)ns[y][1]]);
						Option::putopt(j, i, DEL);
					}
					if (res > dp[y][ljj] + 1) {
						res = dp[y][ljj] + 1;
						Option::putfa(j, i, mapping[(int)ns[y][1]]);
						Option::putopt(j, i, SUB);
					}
				}
				if (res < tmp_res) {
					for (int y, k = 0; k <= nex[i][0]; k++) {
						y = nex[i][k];
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
		if (ans > dp[i][n & 1]) {
			ans = dp[i][n & 1];
			en = i;
		}

	LOG("%d\n", en);
	construct(n, en);

	for (int i = 1; i <= outlen; i++)
		putchar(out[i]);
	printf("\n%d\n", ans);
	
	Option::clearopt();
	calc(s, n, out, outlen, true);
	print_opt(n, outlen);
	return 0;
}
