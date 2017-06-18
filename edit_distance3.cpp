#include <cstdio>
#include <cstring>

#include <string>
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <iostream>

using namespace std;

enum Operation {
	NOP,
	DEL,
	INS,
	SUB
};

const int maxn = 10200;
const int maxm = 10020;
const int maxl = 32;
struct Edge {
	int nex, y;
} e[maxm * 4];
int list[maxm], cnt;
char s[maxn], out[maxn];
char ns[maxm][maxl];
int fa[maxn][maxm];
int dp[maxn][maxm][2];
Operation opt[maxn][maxm];
unordered_map<string, int> M[2];
unordered_map<int, vector<int>> Mv[2];
int n, k, m, tlen, outlen;

#ifdef DEBUG
#define LOG(...) fprintf(stderr, __VA_ARGS__)
#else
#define LOG(...)
#endif

void print_opt(int n, int m) {
	if (n + m == 0)
		return;
	switch (opt[n][m]) {
		case NOP:
			print_opt(n - 1, m - 1);
			break;
		case DEL:
			print_opt(n - 1, m);
			printf("DEL %d\n", n - 1);
			break;
		case INS:
			print_opt(n, m - 1);
			printf("INS %d %c\n", n, s[m]);
			break;
		case SUB:
			print_opt(n - 1, m - 1);
			printf("SUB %d %c\n", n - 1, s[m]);
			break;
	}
}

int start;
void construct(int n, int m) {
	if (n + m == 0) {
		for (int i = 1; i < tlen; i++)
			out[++outlen] = ns[start][i];
		return;
	}
	LOG("%d %d %d\n", n, m, fa[n][m]);
	if (fa[n][m] == 0 && m != 0)
		start = m;
	switch (opt[n][m]) {
		case NOP:
			construct(n - 1, fa[n][m]);
			if (m) out[++outlen] = ns[m][tlen];
			break;
		case DEL:
			construct(n, fa[n][m]);
			if (m) out[++outlen] = ns[m][tlen];
			break;
		case INS:
			construct(n - 1, m);
			break;
		case SUB:
			construct(n - 1, fa[n][m]);
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

//int tmp_dp[2][maxn];
int tmp_dp[maxn][2];
int *calc(char *s, int n, char *t, int m) {
	tmp_dp[0][0] = 0;

	for (int i = 1; i <= n; i++) {
		tmp_dp[i][0] = i;
		opt[i][0] = DEL;
	}
	/*
	for (int i = 1; i <= m; i++) {
		tmp_dp[0][i] = i;
		opt[0][i] = INS;
	}
	*/
	/*
	for (int ii, i = 1; i <= n; i++) {
		ii = i & 1;
		tmp_dp[ii][0] = i;
		opt[i][0] = DEL;
		for (int j = 1; j <= m; j++) {
			if (s[i] == t[j]) {
				tmp_dp[ii][j] = tmp_dp[ii ^ 1][j - 1];
				opt[i][j] = NOP;
			} else {
				if (tmp_dp[ii ^ 1][j] < tmp_dp[ii][j - 1]) {
					tmp_dp[ii][j] = tmp_dp[ii ^ 1][j] + 1;
					opt[i][j] = DEL;
				} else {
					tmp_dp[ii][j] = tmp_dp[ii][j - 1] + 1;
					opt[i][j] = INS;
				}
				if (tmp_dp[ii][j] > tmp_dp[ii ^ 1][j - 1] + 1) {
					tmp_dp[ii][j] = tmp_dp[ii ^ 1][j - 1] + 1;
					opt[i][j] = SUB;
				}
			}
		}
	}
	*/
	static int a[maxn];
	for (int jj, j = 1; j <= m; j++) {
		jj = j & 1;
		tmp_dp[0][jj] = j;
		opt[0][j] = INS;
		for (int i = 1; i <= n; i++) {
			if (s[i] == t[j]) {
				tmp_dp[i][jj] = tmp_dp[i - 1][jj ^ 1];
				opt[i][j] = NOP;
			} else {
				if (tmp_dp[i - 1][jj] < tmp_dp[i][jj ^ 1]) {
					tmp_dp[i][jj] = tmp_dp[i - 1][jj] + 1;
					opt[i][j] = DEL;
				} else {
					tmp_dp[i][jj] = tmp_dp[i][jj ^ 1] + 1;
					opt[i][j] = INS;
				}
				if (tmp_dp[i][jj] > tmp_dp[i - 1][jj ^ 1] + 1) {
					tmp_dp[i][jj] = tmp_dp[i - 1][jj ^ 1] + 1;
					opt[i][j] = SUB;
				}
			}
		}
		a[j] = tmp_dp[n][jj];
		if (a[j] + n == j) {
			a[j] = -1;
			break;
		}
	}
	//return tmp_dp[n & 1];
	return a;
}

int main() {
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
	for (int t, i = 1; i <= m; i++) {
		t = M[1][string(ns[i] + 2)];
		//cout << t << " " << string(ns[i] + 2) << endl;
		for (auto v : Mv[0][t]) {
			addedge(v, i);
			LOG("%d -> %d\n", i, v);
		}
	}
	vector<int> bound[maxm]; // XXX maybe we can use vector<uint8_t>
	memset(dp, 127, sizeof dp);
	for (int i = 1; i <= m; i++) {
		int *a = calc(ns[i], tlen, s, n);
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
	memset(opt, 0, sizeof opt);

	for (int j = 2; j <= n; j++) {
		int cur = j & 1;
		for (int i = 1; i <= m; i++) {
			int &res = dp[j][i][cur];

			// calc dp[j][i][cur ^ 1]
			res = j >= (int)bound[i].size() ? j - tlen : bound[i][j];
			//if (res > dp[j][i][cur ^ 1])
			//	res = dp[j][i][cur ^ 1];
			for (int y, k = list[i]; k; k = e[k].nex) {
				y = e[k].y;
				if (s[j] == ns[i][tlen]) {
					if (res > dp[j - 1][y][cur ^ 1]) {
						res = dp[j - 1][y][cur ^ 1];
						fa[j][i] = y;
						opt[j][i] = NOP;
					}
				} else {
					if (dp[j - 1][i][cur ^ 1] < dp[j][y][cur ^ 1]) {
						if (res > dp[j - 1][i][cur ^ 1] + 1) {
							res = dp[j - 1][i][cur ^ 1] + 1;
							opt[j][i] = INS;
						}
					} else {
						if (res > dp[j][y][cur ^ 1] + 1) {
							res = dp[j][y][cur ^ 1] + 1;
							fa[j][i] = y;
							opt[j][i] = DEL;
						}
					}
					if (res > dp[j - 1][y][cur ^ 1] + 1) {
						res = dp[j - 1][y][cur ^ 1] + 1;
						fa[j][i] = y;
						opt[j][i] = SUB;
					}
				}
			}
		}
	}

	int ans = maxn, en;
	for (int i = 1; i <= m; i++)
		if (ans > dp[n][i][n & 1]) {
			ans = dp[n][i][n & 1];
			en = i;
		}

	LOG("%d\n", en);
	construct(n, en);

	for (int i = 1; i <= outlen; i++)
		putchar(out[i]);
	printf("\n%d\n", ans);
	
	memset(opt, 0, sizeof opt);
	calc(s, n, out, outlen);
	print_opt(n, outlen);
	return 0;
}
