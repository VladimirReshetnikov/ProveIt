"""Exact tail certificates for a harmonic mode contrast.

The observable has normalized eigenvalues +1 (2*k copies) and -1/2
(16*k copies). Its centered Gaussian quadratic form has b=1, v=6*k,
normalized third trace s=0, and normalized fourth trace q=1/2.
At the crossover x=v its probability is the exact rational

    3**(-(9*k-1)) * sum(comb(9*k-1,j)*2**(9*k-1-j), j=0,...,k-1).

No simulation, numerical integration, or optional library is used.
The file prints JSON records, including exact rational certificates.
"""

from fractions import Fraction
from math import comb, log, pi, sqrt
import argparse
import json


def exact_radau_tail(k: int) -> Fraction:
    """P(chi2[2k] >= chi2[16k]/2), exactly, for positive integer k."""
    if not isinstance(k, int) or k < 1:
        raise ValueError("k must be a positive integer")
    n = 9 * k - 1
    numerator = sum(comb(n, j) * (1 << (n - j)) for j in range(k))
    return Fraction(numerator, 3**n)


def log_fraction(value: Fraction) -> float:
    """Stable log even when the rational's value underflows float."""
    return log(value.numerator) - log(value.denominator)


def certificate(k: int) -> dict:
    probability = exact_radau_tail(k)
    v = 6 * k
    exact_rate = (4 / 3) * log(4 / 3) - log(3) / 6
    c_unrestricted = (1 - log(2)) / 2
    golden = (sqrt(5) - 1) / 2
    c_balanced = golden / 2 + log(golden) / 4
    log_p = log_fraction(probability)
    last = Fraction(comb(9*k-1, k-1) * 2**(8*k), 3**(9*k-1))
    backward_ratio = Fraction(2 * (k - 1), 8 * k + 1)
    # Every preceding-term ratio is at most backward_ratio.
    assert last <= probability <= last / (1 - backward_ratio)
    return {
        "k": k,
        "matrix_dimension": 18 * k,
        "v": v,
        "threshold": v,
        "s": 0,
        "q": 0.5,
        "exact_probability_numerator": str(probability.numerator),
        "exact_probability_denominator": str(probability.denominator),
        "log_exact_probability": log_p,
        "negative_log_probability_over_v": -log_p / v,
        "unrestricted_exponent_over_v": c_unrestricted,
        "signed_exponent_over_v": c_balanced,
        "radau_exact_exponent_over_v": exact_rate,
        "predicted_log_probability_with_prefactor": (
            -v * exact_rate - log(3) - 0.5 * log(pi * k)
        ),
        "log_ratio_to_leading_asymptotic": (
            log_p + v * exact_rate + log(3) + 0.5 * log(pi * k)
        ),
        "exact_ratio_to_last_binomial_term": str(probability / last),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--k", type=int, nargs="+", default=[1, 2, 4, 8, 16, 32, 64, 128])
    args = parser.parse_args()
    assert exact_radau_tail(1) == Fraction(256, 6561)
    for k in args.k:
        print(json.dumps(certificate(k), sort_keys=True))


if __name__ == "__main__":
    main()
