// Exact Apéry Hankel determinants, C++17 and GMP.
// Build: g++ -O3 -std=c++17 apery_gmp.cpp -lgmpxx -lgmp -o apery_gmp
// Usage: ./apery_gmp N [stride=1] [shift=0] > determinants.txt
// All divisions are checked; no floating-point determinant is used.
#include <gmpxx.h>
#include <chrono>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Z = mpz_class;

static long argument(const char* text, long minimum) {
    std::size_t used = 0;
    std::string s(text);
    long n = std::stol(s, &used);
    if (used != s.size() || n < minimum)
        throw std::invalid_argument("invalid integer argument");
    return n;
}

static Z divide_exact(const Z& numerator, const Z& denominator) {
    if (denominator == 0 ||
        !mpz_divisible_p(numerator.get_mpz_t(), denominator.get_mpz_t()))
        throw std::runtime_error("nonexact division");
    Z out;
    mpz_divexact(out.get_mpz_t(), numerator.get_mpz_t(), denominator.get_mpz_t());
    return out;
}

int main(int argc, char** argv) {
    try {
        if (argc < 2 || argc > 4) {
            std::cerr << "Usage: " << argv[0] << " N [stride=1] [shift=0]\n";
            return 2;
        }
        long n = argument(argv[1], 0);
        long stride = argc > 2 ? argument(argv[2], 1) : 1;
        long shift = argc > 3 ? argument(argv[3], 0) : 0;
        // Defensive resource limit; remove only after considering quadratic storage.
        if (n > 2000 || stride > 1000 || shift > 100000)
            throw std::invalid_argument("resource guard exceeded");
        long last = 2 * stride * n + shift;
        std::vector<Z> moments(last + 1);
        moments[0] = 1;
        if (last >= 1) moments[1] = 5;
        for (long k = 1; k < last; ++k) {
            Z t(k);
            Z numerator = (2*t+1)*(17*t*t+17*t+5)*moments[k]
                          - t*t*t*moments[k-1];
            Z denominator = (t+1)*(t+1)*(t+1);
            moments[k+1] = divide_exact(numerator, denominator);
        }
        const auto start = std::chrono::steady_clock::now();
        const long order = n + 1;
        std::vector<std::vector<Z>> a(order, std::vector<Z>(order));
        for (long i = 0; i < order; ++i)
            for (long j = 0; j < order; ++j)
                a[i][j] = moments[stride*(i+j)+shift];
        Z previous(1);
        unsigned long long divisions = 0;
        std::cout << "# index exact_determinant\n";
        for (long k = 0; k < n; ++k) {
            const Z pivot = a[k][k];
            if (pivot <= 0) throw std::runtime_error("nonpositive leading pivot");
            std::cout << k << ' ' << pivot << '\n';
            for (long i = k+1; i < order; ++i) {
                const Z aik = a[i][k];
                for (long j = i; j < order; ++j) {
                    Z numerator = pivot*a[i][j] - aik*a[k][j];
                    Z value = divide_exact(numerator, previous);
                    a[i][j] = value;
                    a[j][i] = value;
                    ++divisions;
                }
            }
            for (long i = k+1; i < order; ++i)
                a[i][k] = a[k][i] = 0;
            previous = pivot;
            if ((k+1) % 25 == 0)
                std::cerr << "completed pivot " << k+1 << '/' << n << '\n';
        }
        if (a[n][n] <= 0) throw std::runtime_error("nonpositive final pivot");
        std::cout << n << ' ' << a[n][n] << '\n';
        auto elapsed = std::chrono::duration<double>(
            std::chrono::steady_clock::now()-start).count();
        std::cerr << "checked_exact_divisions=" << divisions
                  << " determinant_seconds=" << elapsed << '\n';
    } catch (const std::exception& ex) {
        std::cerr << "error: " << ex.what() << '\n';
        return 2;
    }
}
