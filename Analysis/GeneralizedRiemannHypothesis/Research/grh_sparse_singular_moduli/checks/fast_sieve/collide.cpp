#include "quotient.hpp"

// Enumerate 0 <= a <= b <= c <= d < period. The distinguished exponent zero
// precedes this quadruple, even when one of its four entries is itself zero.
int main(int argc, char** argv) {
    if (argc != 3) return 2;
    const ColumnTable first_prime(argv[1]), second_prime(argv[2]);
    if (first_prime.period != second_prime.period) return 3;
    const int period = first_prime.period;
    Wide reported = 0;

    std::vector<int> first_key(period), second_key(period);
    std::vector<std::pair<int, int>> sorted_keys(period);
    for (int a = 0; a < period; ++a) {
        for (int b = a; b < period; ++b) {
            const ColumnQuotient first_quotient(first_prime, a, b);
            const ColumnQuotient second_quotient(second_prime, a, b);
            for (int d = b + 1; d < period; ++d) {
                first_key[d] = first_quotient.projective_key(first_prime.columns[d][0]);
                second_key[d] = second_quotient.projective_key(second_prime.columns[d][0]);
                sorted_keys[d] = {first_key[d], d};
            }
            const auto start = sorted_keys.begin() + b + 1;
            std::sort(start, sorted_keys.end());

            for (int c = b; c < period; ++c) {
                // Prior occurrences of a residue determine the confluent order.
                const int order = (c == 0) + (c == a) + (c == b);
                const int left_first = c > b ? first_key[c]
                    : first_quotient.projective_key(first_prime.columns[c][order]);
                const int left_second = c > b ? second_key[c]
                    : second_quotient.projective_key(second_prime.columns[c][order]);

                auto report = [&](int d) {
                    std::cout << a << ' ' << b << ' ' << c << ' ' << d << '\n';
                    ++reported;
                };

                // For d=c the second occurrence uses order+1 at both primes.
                const int repeat_first = first_quotient.projective_key(first_prime.columns[c][order+1]);
                const int repeat_second = second_quotient.projective_key(second_prime.columns[c][order+1]);
                if (dependent_keys(left_first, repeat_first) && dependent_keys(left_second, repeat_second))
                    report(c);

                auto check_second_prime = [&](int d) {
                    if (d > c && dependent_keys(left_second, second_key[d])) report(d);
                };
                if (left_first == 0) {
                    for (int d = c + 1; d < period; ++d) check_second_prime(d);
                    continue;
                }

                // At the first prime only a zero vector or a matching projective
                // line can fail. Sorted keys locate both sets of candidate d's.
                for (auto it = start; it != sorted_keys.end() && it->first == 0; ++it)
                    check_second_prime(it->second);
                const auto target = std::make_pair(left_first, c+1);
                auto it = std::lower_bound(start, sorted_keys.end(), target);
                for (; it != sorted_keys.end() && it->first == left_first; ++it)
                    check_second_prime(it->second);
            }
        }
    }
    std::cerr << reported << " simultaneous failures modulo " << period << '\n';
}
