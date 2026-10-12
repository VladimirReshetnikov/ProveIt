#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>

// Exact arithmetic in F_p, p=2^31-1. No floating-point operations.
using u32 = std::uint32_t;
using u64 = std::uint64_t;
constexpr u64 prime = 2147483647ULL;

u32 reduce(u64 x) {
    x = (x & prime) + (x >> 31);
    x = (x & prime) + (x >> 31);
    return static_cast<u32>(x >= prime ? x - prime : x);
}
u32 multiply(u32 x, u32 y) { return reduce(static_cast<u64>(x) * y); }
u32 power(u32 x, u64 e) {
    u32 y = 1;
    for (; e; e >>= 1, x = multiply(x, x))
        if (e & 1) y = multiply(y, x);
    return y;
}
u32 inverse(u32 x) {
    if (!x) throw std::runtime_error("A denominator vanishes modulo p.");
    return power(x, prime - 2);
}
u32 falling(int n, int order) {
    u32 x = 1;
    for (int k = 0; k < order; ++k) x = multiply(x, n - k);
    return x;
}
bool is_prime(u64 p) {
    if (p < 2) return false;
    for (u64 d = 2; d * d <= p; ++d)
        if (p % d == 0) return false;
    return true;
}
u32 determinant(std::vector<std::vector<u32>> a) {
    const int m = a.size();
    u32 det = 1;
    for (int k = 0; k < m; ++k) {
        int pivot = k;
        while (pivot < m && !a[pivot][k]) ++pivot;
        if (pivot == m) return 0;
        if (pivot != k) {
            std::swap(a[pivot], a[k]);
            det = det ? prime - det : 0;
        }
        det = multiply(det, a[k][k]);
        const u32 pivot_inverse = inverse(a[k][k]);
        for (int i = k + 1; i < m; ++i) {
            const u32 factor = multiply(a[i][k], pivot_inverse);
            for (int j = k + 1; j < m; ++j)
                a[i][j] = reduce(a[i][j] + prime - multiply(factor, a[k][j]));
        }
    }
    return det;
}

int main(int argc, char **argv) {
    const int m = argc > 1 ? std::atoi(argv[1]) : 4;
    const int threshold = argc > 2 ? std::atoi(argv[2]) : 8192;
    if (m < 1 || m > 8 || threshold <= m + 1)
        throw std::runtime_error("Require 1 <= m <= 8 and threshold > m+1.");
    if (!is_prime(prime)) throw std::runtime_error("Primality check failed.");
    const int last = threshold + m - 1;
    if (2ULL * last + 1 >= prime)
        throw std::runtime_error("The small-denominator hypothesis fails.");

    std::vector<u32> beta(last + 1), a(last + 1), b(last + 1), diagonal(last + 1);
    beta[1] = inverse(6);
    for (int n = 2; n < last; ++n) {
        u64 sum = 0;
        for (int k = 1; 2 * k < n; ++k)
            sum += 2ULL * multiply(beta[k], beta[n - k]);
        if (!(n & 1)) sum += multiply(beta[n / 2], beta[n / 2]);
        beta[n] = multiply(reduce(sum), inverse(2 * (2 * n + 1)));
    }

    // Independent cotangent check by formal multiplication with sine.
    // beta is from the nonlinear Riccati recurrence; these coefficients
    // come directly from the Taylor series of cos(sqrt(t)/2) and
    // sin(sqrt(t)/2)/(sqrt(t)/2).
    u32 cosine = 1, sine = 1;
    std::vector<u32> sine_coeff(last), cosine_coeff(last);
    sine_coeff[0] = cosine_coeff[0] = 1;
    for (int n = 1; n < last; ++n) {
        cosine = multiply(prime - cosine,
                          inverse(reduce(4ULL * (2 * n - 1) * (2 * n))));
        sine = multiply(prime - sine,
                        inverse(reduce(4ULL * (2 * n) * (2 * n + 1))));
        cosine_coeff[n] = cosine;
        sine_coeff[n] = sine;
    }
    const u32 inv_two = inverse(2);
    for (int n = 1; n < last; ++n) {
        u64 convolution = 0;
        for (int k = 1; k <= n; ++k)
            convolution += multiply(beta[k], sine_coeff[n - k]);
        const u32 recovered = reduce(sine_coeff[n] + prime
                                    - multiply(inv_two, reduce(convolution)));
        if (recovered != cosine_coeff[n])
            throw std::runtime_error("Independent sine/cosine check failed.");
    }

    std::vector<std::array<u32, 8>> r(last + 1);
    for (int n = 1; n <= m; ++n) r[n][n - 1] = 1;
    for (int n = m + 1; n <= last; ++n) {
        a[n] = falling(2 * n, 2 * m);
        b[n] = falling(2 * n - 1, 2 * m);
        diagonal[n] = reduce(2ULL * (static_cast<u64>(a[n]) + b[n]));
        const u32 factored = multiply(multiply(multiply(2, a[n]), 2 * n - m), inverse(n));
        if (diagonal[n] != factored || !diagonal[n])
            throw std::runtime_error("Diagonal factorization failed.");
        const u32 inv_diagonal = inverse(diagonal[n]);
        std::array<u64, 8> sum{};
        for (int u = 1; u < n; ++u) {
            const u32 weight = multiply(beta[n - u], reduce(b[n] + static_cast<u64>(a[u])));
            for (int j = 0; j < m; ++j) sum[j] += multiply(weight, r[u][j]);
        }
        for (int j = 0; j < m; ++j) r[n][j] = multiply(reduce(sum[j]), inv_diagonal);
    }

    std::cout << "{\"half_gap\":" << m << ",\"prime\":" << prime
              << ",\"threshold\":" << threshold
              << ",\"primality_checked\":true,\"cotangent_coefficients_checked\":"
              << last - 1 << ",\"residues\":[";
    int failures = 0;
    for (int cutoff = m + 1; cutoff < threshold; ++cutoff) {
        std::vector<std::vector<u32>> matrix(m, std::vector<u32>(m));
        for (int i = 0; i < m; ++i)
            for (int j = 0; j < m; ++j) matrix[i][j] = r[cutoff + i + 1][j];
        const u32 det = determinant(matrix);
        failures += det == 0;
        if (cutoff != m + 1) std::cout << ',';
        std::cout << '[' << cutoff << ',' << det << ']';
    }
    std::cout << "],\"zero_residues\":" << failures << "}\n";
    return failures ? 1 : 0;
}
