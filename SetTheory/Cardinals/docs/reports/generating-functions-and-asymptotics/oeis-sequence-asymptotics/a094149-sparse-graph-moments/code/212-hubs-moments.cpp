// Exact first-edge recurrence used by Report212.
// Arithmetic/loop ordering follow the checkpoint implementation. The CLI and
// file I/O are hardened here; no floating-point arithmetic is used.
#include <gmpxx.h>
#include <charconv>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using Integer = mpz_class;

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "GENERATOR_FAILED[argument]: usage: moments N (1<=N<=512)\n";
        return 2;
    }
    int n = 0;
    const std::string argument(argv[1]);
    const auto parsed = std::from_chars(argument.data(), argument.data()+argument.size(), n);
    if (parsed.ec != std::errc() || parsed.ptr != argument.data()+argument.size() || n<1 || n>512) {
        std::cerr << "GENERATOR_FAILED[argument]: N must be an integer in [1,512]\n";
        return 2;
    }
    std::string phase = "allocation";
    try {
        std::vector<std::vector<Integer>> c(2*n+1, std::vector<Integer>(2*n+1));
        for (int i=0; i<=2*n; ++i) {
            c[i][0] = c[i][i] = 1;
            for (int j=1; j<i; ++j) c[i][j] = c[i-1][j]+c[i-1][j-1];
        }
        std::vector<std::vector<Integer>> f(n+1, std::vector<Integer>(n+1));
        std::vector<std::vector<Integer>> e(n+1, std::vector<Integer>(n+1));
        f[0][0] = 1;
        for (int q=1; q<=n; ++q) e[0][q] = 1;
        std::ofstream out, roots;
        out.exceptions(std::ios::failbit | std::ios::badbit);
        roots.exceptions(std::ios::failbit | std::ios::badbit);
        phase = "open";
        out.open("moments_exact.tsv", std::ios::out | std::ios::trunc);
        roots.open("root_counts_exact.tsv", std::ios::out | std::ios::trunc);
        phase = "write";
        out << "k\tM2k\n0\t1\n";
        roots << "k\tm\tcount\n";
        for (int k=1; k<=n; ++k) {
            for (int q=1; q<=k; ++q) {
                for (int a=0; a<=k-q; ++a) {
                    const int b = k-q-a;
                    for (int mb=0; mb<=b; ++mb) {
                        if (f[b][mb] == 0) continue;
                        f[k][q+mb] += e[a][q]*f[b][mb]*c[mb+q-1][q-1];
                    }
                }
            }
            for (int q=1; q<=n-k; ++q)
                for (int m=1; m<=k; ++m)
                    e[k][q] += f[k][m]*c[m+q-1][q-1];
            Integer total = 0;
            for (int m=1; m<=k; ++m) total += f[k][m];
            out << k << '\t' << total << '\n';
            for (int m=1; m<=k; ++m) roots << k << '\t' << m << '\t' << f[k][m] << '\n';
            if (k%10 == 0) {
                std::cerr << k << '\n';
                out.flush();
                roots.flush();
            }
        }
        // Explicit flush and close catch delayed disk/write failures as well.
        out.flush();
        roots.flush();
        phase = "close";
        out.close();
        roots.close();
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "GENERATOR_FAILED[" << phase << "]: " << error.what() << '\n';
        return 1;
    }
}
