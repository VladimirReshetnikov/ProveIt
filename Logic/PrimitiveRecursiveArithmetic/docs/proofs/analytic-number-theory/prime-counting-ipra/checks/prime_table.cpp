// Reproduce pi(10^e) by Lehmer's exact fourth-root formula.
// Build: c++ -O3 -std=c++17 prime_table.cpp -o prime_table
// Run:   ./prime_table [maximum exponent, 1..14; default 14]
// A separate descending quotient-table sieve cross-checks e <= 10.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

using U64 = std::uint64_t;
using I64 = std::int64_t;
using U32 = std::uint32_t;
constexpr U64 input_limit = 100000000000000ULL;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}

U64 isqrt(U64 n) {
    // The floating-point seed only affects speed. Division checks certify r.
    U64 r = static_cast<U64>(std::sqrt(static_cast<double>(n)));
    while (r > 0 && r > n / r) --r;
    while (r + 1 <= n / (r + 1)) ++r;
    return r;
}

U64 icbrt(U64 n) {
    U64 r = static_cast<U64>(std::cbrt(static_cast<double>(n)));
    while (r > 0 && r > n / r / r) --r;
    while (r + 1 <= n / (r + 1) / (r + 1)) ++r;
    return r;
}

class Lehmer {
    // Dense Phi rows cover small subproblems. Row 6 also covers one wheel.
    static constexpr unsigned phi_n = 65536, phi_a = 64;
    static constexpr unsigned wheel_a = 6, wheel = 30030;
    std::vector<U32> pi_small;
    std::vector<U32> primes;
    std::vector<std::vector<U32>> rows;
    std::unordered_map<U64, U64> pi_cache;

    U64 phi(U64 x, unsigned a) const {
        if (a == 0) return x;
        if (a <= phi_a && x <= phi_n) return rows[a][x];
        if (a == wheel_a) {
            return (x / wheel) * rows[a][wheel] + rows[a][x % wheel];
        }
        const U64 p = primes[a - 1];
        if (x < p) return x > 0;
        if (x < pi_small.size() && x / p < p) {
            return 1 + pi_small[x] - a;
        }
        return phi(x, a - 1) - phi(x / p, a - 1);
    }

public:
    explicit Lehmer(U64 limit) {
        require(limit <= input_limit, "unsupported input");
        const U64 size = std::max<U64>(isqrt(limit), phi_n);
        pi_small.resize(size + 1);
        std::vector<bool> flags(size + 1, true);
        flags[0] = flags[1] = false;
        for (U64 p = 2; p <= size / p; ++p) {
            if (flags[p]) {
                for (U64 t = p*p; t <= size; t += p) flags[t] = false;
            }
        }
        for (U64 n = 2; n <= size; ++n) {
            pi_small[n] = pi_small[n - 1] + flags[n];
            if (flags[n]) primes.push_back(n);
        }
        require(primes.size() >= phi_a, "prime prefix too short");
        rows.assign(phi_a + 1, std::vector<U32>(phi_n + 1));
        for (unsigned n = 0; n <= phi_n; ++n) rows[0][n] = n;
        for (unsigned a = 1; a <= phi_a; ++a) {
            for (unsigned n = 0; n <= phi_n; ++n) {
                rows[a][n] = rows[a - 1][n] - rows[a - 1][n / primes[a - 1]];
            }
        }
    }

    U64 count(U64 x) {
        if (x < pi_small.size()) return pi_small[x];
        const auto saved = pi_cache.find(x);
        if (saved != pi_cache.end()) return saved->second;
        const U64 s = isqrt(x);
        require(s < pi_small.size(), "sqrt exceeds stored prime range");
        const I64 a = pi_small[isqrt(s)];
        const I64 b = pi_small[s];
        const I64 c = pi_small[icbrt(x)];
        // b <= 10^7, x <= 10^14, so both this product and sum fit in int64.
        I64 sum = static_cast<I64>(phi(x, a)) + (b + a - 2)*(b - a + 1)/2;
        // Formula indices a+1,...,b become zero-based indices a,...,b-1.
        for (I64 i = a; i < b; ++i) {
            const U64 w = x / primes[i];
            sum -= static_cast<I64>(count(w));
            if (i < c) {
                const I64 end = pi_small[isqrt(w)];
                for (I64 j = i; j < end; ++j) {
                    sum -= static_cast<I64>(count(w / primes[j])) - j;
                }
            }
            require(sum >= 0, "negative count in Lehmer formula");
        }
        require(static_cast<U64>(sum) <= x, "count exceeds input");
        pi_cache.emplace(x, sum);
        return sum;
    }
};

// Independent sieve on Q = {floor(n/i): 1 <= i <= n}. Keys are descending.
// S(v) counts primes already processed plus surviving integers in [2,v].
U64 quotient_sieve(U64 n) {
    require(n >= 2 && n <= 10000000000ULL, "quotient cross-check range");
    const U64 r = isqrt(n);
    std::vector<U64> keys, sums;
    for (U64 i = 1; i <= n;) {
        const U64 v = n/i;
        keys.push_back(v);
        sums.push_back(v - 1);
        i = n/v + 1;
    }
    const auto index = [&](U64 v) -> std::size_t {
        return v <= r ? keys.size() - v : n/v - 1;
    };
    for (U64 p = 2; p <= r; ++p) {
        const U64 before = sums[index(p - 1)];
        if (sums[index(p)] == before) continue;
        for (std::size_t i = 0; i < keys.size() && keys[i] >= p*p; ++i) {
            const U64 high = sums[index(keys[i]/p)];
            require(before <= high && high - before <= sums[i],
                    "quotient sieve underflow");
            sums[i] -= high - before;
        }
    }
    return sums.front();
}

int main(int argc, char** argv) {
    const int last = argc == 2 ? std::stoi(argv[1]) : 14;
    require(argc <= 2 && 1 <= last && last <= 14, "expected exponent 1..14");
    U64 bound = 1;
    for (int e = 0; e < last; ++e) bound *= 10;
    Lehmer lehmer(bound);
    const std::vector<U64> published = {
        0, 4, 25, 168, 1229, 9592, 78498, 664579, 5761455, 50847534,
        455052511, 4118054813ULL, 37607912018ULL, 346065536839ULL,
        3204941750802ULL
    };
    std::cout << "e  pi(10^e)  independent quotient sieve\n";
    U64 x = 1;
    for (int e = 1; e <= last; ++e) {
        x *= 10;
        const U64 value = lehmer.count(x);
        require(value == published[e], "mismatch with published value");
        if (e <= 10) {
            require(value == quotient_sieve(x), "quotient cross-check mismatch");
        }
        std::cout << e << "  " << value << "  "
                  << (e <= 10 ? "agrees" : "-") << std::endl;
    }
}
