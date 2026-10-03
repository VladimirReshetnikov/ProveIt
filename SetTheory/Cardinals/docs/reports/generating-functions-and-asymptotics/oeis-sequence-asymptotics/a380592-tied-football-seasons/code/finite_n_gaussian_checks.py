#!/usr/bin/env python3
"""Evaluate exact-rational finite-n Gaussian cumulants.

The displayed decimals are diagnostics, not a fitted asymptotic proof.
The exported rational values are compared exactly by replay.py.
"""

from functools import lru_cache

from gaussian_moments import L, P, S, distinct_moment, grouped_partitions, n
from output_support import write_result


@lru_cache(None)
def exact_moment(degrees, size):
    if sum(degrees) % 2:
        return S.Integer(0)
    a = S.Rational(9, 28 * size - 2)
    b = (S.Rational(9, 2 * (size - 1)) - a) / size
    answer = S.Integer(0)
    for blocks, multiplicity in grouped_partitions(degrees):
        falling_factorial = S.prod(size - j for j in range(len(blocks)))
        answer += multiplicity * falling_factorial * sum(
            coefficient * a**power_a * b**power_b
            for (power_a, power_b), coefficient in distinct_moment(blocks)
        )
    return answer


def main():
    poly = sum(L.values())
    terms = {j: S.Poly(S.expand(poly**j), n, *P[1:]).terms() for j in range(1, 5)}
    result = []
    for size in (20, 50, 100, 1000):
        means = {0: S.Integer(1)}
        for j in range(1, 5):
            value = S.Integer(0)
            for powers, coefficient in terms[j]:
                degrees = tuple(
                    degree for degree, count in enumerate(powers[1:], 1)
                    for _ in range(count)
                )
                value += coefficient * size**powers[0] * exact_moment(degrees, size)
            means[j] = value
        cumulants = {}
        for j in range(1, 5):
            cumulants[j] = means[j] - sum(
                S.binomial(j - 1, k - 1) * cumulants[k] * means[j - k]
                for k in range(1, j)
            )
        log_four = sum(cumulants[j] / S.factorial(j) for j in range(1, 5))
        scaled = size * (log_four + S.Rational(7865, 32928))
        row = {
            "n": size,
            "first_four_exact_gaussian_cumulants": str(S.N(log_four, 20)),
            "n_times_difference_from_limit": str(S.N(scaled, 20)),
            "target_first_coefficient": str(S.N(S.Rational(1147975, 45177216), 20)),
            "exact_log_local_integral_through_four_cumulants": str(log_four),
            "exact_n_times_difference_from_limit": str(scaled),
        }
        result.append(row)
        print(f"n={size}: {row['n_times_difference_from_limit']}", flush=True)
    print(write_result("finite_n_gaussian_checks", result))


if __name__ == "__main__":
    main()
