"""Rigorous rational enclosures for the density and mean-preperiod formulas.

No floating point is used in the enclosures. Decimal output is rounded outwards.
The zeta enclosure uses an Euler-transformed eta series, whose omitted positive
terms have total at most 2**(-terms). See Appendix B of article.pdf.
"""

import argparse
import json
import sys
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

from secant_periodicity import density_cutoff, factor_integer, secant_numbers


@lru_cache(maxsize=None)
def zeta_interval(s: int, terms: int = 96):
    if s < 2 or terms < 1:
        raise ValueError("s>=2 and terms>=1 are required")
    row = [Fraction(1, (j + 1) ** s) for j in range(terms)]
    partial = Fraction(0)
    for k in range(terms):
        if row[0] <= 0:
            raise AssertionError("Euler difference must be positive")
        partial += row[0] / (2 ** (k + 1))
        row = [row[j] - row[j + 1] for j in range(len(row) - 1)]
    denominator = 1 - Fraction(1, 2 ** (s - 1))
    return partial / denominator, (partial + Fraction(1, 2 ** terms)) / denominator


def outward(value: Fraction, digits: int, upper: bool) -> str:
    with localcontext() as context:
        context.prec = max(100, digits + 30)
        context.rounding = ROUND_CEILING if upper else ROUND_FLOOR
        decimal = Decimal(value.numerator) / Decimal(value.denominator)
        return format(decimal.quantize(Decimal(1).scaleb(-digits)), "f")


def serialize(lower: Fraction, upper: Fraction):
    if lower > upper:
        raise AssertionError("reversed interval")
    return {
        "lower": {"numerator": str(lower.numerator), "denominator": str(lower.denominator)},
        "upper": {"numerator": str(upper.numerator), "denominator": str(upper.denominator)},
        "decimal_lower": outward(lower, 30, False),
        "decimal_upper": outward(upper, 30, True),
    }


def main() -> None:
    # Only locally generated exact certificate integers are serialized.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).parent / "data")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    K = 10
    values = secant_numbers(20)
    result = {"method": "positive Euler transform of eta; rational arithmetic",
              "eta_terms": 96, "density_indices": [], "finite_mean_cutoff": K}
    mean_lower = mean_upper = Fraction(1)
    for N in range(1, K + 1):
        s = 2 * N + 1
        factors = factor_integer(values[N])
        cutoff_data = []
        correction = Fraction(1)
        for prime in factors:
            if prime == 2:
                continue
            cutoff = density_cutoff(N, prime, values)
            cutoff_data.append({"prime": prime, "exponent_in_a_N": factors[prime],
                                "maximum_allowed_modulus_exponent": cutoff})
            correction *= ((1 - Fraction(1, prime ** (cutoff + 1))) /
                           (1 - Fraction(1, prime ** s)))
        zeta_lower, zeta_upper = zeta_interval(s)
        base = 1 - Fraction(1, 2 ** s)
        lower, upper = correction / (base * zeta_upper), correction / (base * zeta_lower)
        mean_lower += 1 - upper
        mean_upper += 1 - lower
        entry = {"N": N, "a_N": values[N], "exceptional_primes": cutoff_data,
                 "density_interval": serialize(lower, upper)}
        result["density_indices"].append(entry)
        print("D_{} in [{}, {}]".format(N, outward(lower, 22, False), outward(upper, 22, True)))

    # For N>K, the p=3 contribution is an exact lower bound for 1-D_N.
    tail_exponent = 2 * K + 3
    tail_lower = Fraction(9, 8 * 3 ** tail_exponent)
    _, zeta_tail_upper = zeta_interval(tail_exponent)
    tail_upper = Fraction(9, 8) * ((1 - Fraction(1, 2 ** tail_exponent)) * zeta_tail_upper - 1)
    mean_lower += tail_lower
    mean_upper += tail_upper
    result["mean_preperiod_interval"] = serialize(mean_lower, mean_upper)
    result["remaining_mean_tail_interval"] = serialize(tail_lower, tail_upper)
    target_lower = Fraction(105402581008837151, 10 ** 17)
    target_upper = Fraction(105402581008837162, 10 ** 17)
    if not (target_lower < mean_lower <= mean_upper < target_upper):
        raise AssertionError("the advertised mean-preperiod enclosure was not certified")
    result["advertised_certified_interval"] = ["1.05402581008837151", "1.05402581008837162"]
    (args.output / "density_certificates.json").write_text(json.dumps(result, indent=2) + "\n")
    print("Mean in [{}, {}]".format(outward(mean_lower, 24, False), outward(mean_upper, 24, True)))
    print("All density enclosures certified using exact rational arithmetic.")


if __name__ == "__main__":
    main()
