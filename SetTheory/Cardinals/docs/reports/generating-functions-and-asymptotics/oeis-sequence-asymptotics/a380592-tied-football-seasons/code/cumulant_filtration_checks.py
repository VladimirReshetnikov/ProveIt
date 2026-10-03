#!/usr/bin/env python3
"""Verify Gaussian cumulants through six to constant and 1/n order.

These finite algebraic checks complement the analytic remainder argument;
passing them does not itself establish the asymptotic remainder bounds.
"""

from gaussian_moments import L, S, add, expectation, multiply, scale
from output_support import write_result


def main():
    # Retain at most one L5/L6 factor. The analytic omission bounds belong
    # to the report; this script verifies the resulting finite algebra.
    means = {0: (S.Integer(1), S.Integer(0))}
    for j in range(1, 7):
        means[j] = expectation(
            (L[3] + L[4])**j
            + j * (L[3] + L[4])**(j - 1) * (L[5] + L[6])
        )
        print(f"Moment {j}: {means[j]}", flush=True)
    cumulants = {}
    for j in range(1, 7):
        cumulants[j] = add(
            means[j],
            *[
                scale(multiply(cumulants[k], means[j - k]), -S.binomial(j - 1, k - 1))
                for k in range(1, j)
            ],
        )
    assert cumulants[5] == (0, 0) and cumulants[6] == (0, 0)
    answer = add(*[scale(cumulants[j], 1 / S.factorial(j)) for j in range(1, 7)])
    assert answer == (-S.Rational(7865, 32928), S.Rational(1147975, 45177216))
    result = {
        "raw_moments": {j: [str(v) for v in value] for j, value in means.items()},
        "cumulants": {j: [str(v) for v in value] for j, value in cumulants.items()},
        "log_local_integral": [str(v) for v in answer],
    }
    print(write_result("cumulant_filtration_checks", result))


if __name__ == "__main__":
    main()
