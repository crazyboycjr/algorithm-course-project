#include <cstdio>
#include <cstring>

using namespace std;

enum Operation {
	NOP,
	DEL,
	INS,
	SUB
};

const int maxn = 10200;
char s[2][maxn];
int dp[maxn][maxn];
Operation opt[maxn][maxn];
int n, m;

void printOpt(int n, int m) {
	if (n == 0 && m == 0)
		return;
	switch (opt[n][m]) {
		case NOP:
			printOpt(n - 1, m - 1);
			break;
		case DEL:
			printOpt(n - 1, m);
			printf("DEL %d\n", n - 1);
			break;
		case INS:
			printOpt(n, m - 1);
			printf("INS %d %c\n", n, s[1][m]);
			break;
		case SUB:
			printOpt(n - 1, m - 1);
			printf("SUB %d %c\n", n - 1, s[1][m]);
			break;
	}
}

int main() {
	scanf("%s\n%s\n", s[0] + 1, s[1] + 1);
	n = strlen(s[0] + 1);
	m = strlen(s[1] + 1);
	dp[0][0] = 0;
	for (int i = 1; i <= n; i++) {
		dp[i][0] = i;
		opt[i][0] = DEL;
	}
	for (int i = 1; i <= m; i++) {
		dp[0][i] = i;
		opt[0][i] = INS;
	}
	for (int i = 1; i <= n; i++)
		for (int j = 1; j <= m; j++) {
			if (s[0][i] == s[1][j]) {
				dp[i][j] = dp[i - 1][j - 1];
				opt[i][j] = NOP;
			} else {
				if (dp[i - 1][j] < dp[i][j - 1]) {
					dp[i][j] = dp[i - 1][j] + 1;
					opt[i][j] = DEL;
				} else {
					dp[i][j] = dp[i][j - 1] + 1;
					opt[i][j] = INS;
				}
				if (dp[i][j] > dp[i - 1][j - 1] + 1) {
					dp[i][j] = dp[i - 1][j - 1] + 1;
					opt[i][j] = SUB;
				}
			}
		}
	printf("%d\n", dp[n][m]);
	printOpt(n, m);
	return 0;
}
