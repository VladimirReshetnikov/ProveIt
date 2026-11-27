"""Exact two-prime certificate for the second difference of translated zeta divisors.

For 0 < h <= 1 put b_p(h) = (log p)/sqrt(p) * (1-exp(i h log p))^2/h^2.
At h=0 its continuous limit is -(log p)^3/sqrt(p).
The centered second difference has the same absolute symbol.
Only the standard Python library is required.
"""
import argparse
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


def log_interval(p, terms=6):
    """Bound log p via 2*atanh((p-1)/(p+1)) and its positive series tail."""
    x = Fraction(p - 1, p + 1)
    lower = 2 * sum(x ** (2 * j + 1) / (2 * j + 1) for j in range(terms))
    error = 2 * x ** (2 * terms + 1) / ((2 * terms + 1) * (1 - x**2))
    return lower, lower + error


def main():
    # For 0<=x<=0.55, sin(x)/x >= 1-x^2/6, with sinc(0)=1.
    # This follows also by integrating cos(t)>=1-t^2/2.
    # Here x=h log(p)/2. The modulus squared of the normalized symbol is
    # (log p)^6 * sinc(x)^4 / p, including the value at h=0.
    bounds = [
        (2, Fraction(69, 100), Fraction(70, 100), Fraction(49, 1000)),
        (3, Fraction(109, 100), Fraction(110, 100), Fraction(454, 1000)),
    ]
    total = Fraction(0)
    for p, lo, hi, target in bounds:
        actual_lo, actual_hi = log_interval(p)
        assert lo < actual_lo < actual_hi < hi and hi <= Fraction(11, 10)
        lower = lo**6 * (1 - hi**2 / 24)**4 / p
        assert lower > target
        total += lower
        print(f"p={p}: certified log interval ({lo}, {hi})")
        print(f"  squared coefficient > {lower} > {target}")
    assert total > Fraction(1, 2)
    print(f"Squared norm lower bound = {total} > 1/2 throughout 0 <= h <= 1.")
    print("Thus the two-prime coefficient vector has norm > 1/sqrt(2),")
    print("including at h=0 under the derivative interpretation.")


def zero_table_diagnostic():
    # Numerical provenance is recorded in window_demo.txt. The following count
    # is exact for the supplied rational decimals and has explicit gap slack.
    path = Path(__file__).resolve().with_name("zeta_ordinates.txt")
    ordinates = [Decimal(line.split()[1]) for line in path.read_text().splitlines()
                 if line and not line.startswith("#")]
    uncertainty = Decimal("0.000001")
    left, right = Decimal(27), Decimal(183)
    assert ordinates[0] < left - 2 and ordinates[-1] > right + 1
    isolated = [i + 1 for i in range(1, len(ordinates) - 1)
                if left + 1 + uncertainty < ordinates[i] < right - 1 - uncertainty
                and ordinates[i] - ordinates[i - 1] > 2 + 2 * uncertainty
                and ordinates[i + 1] - ordinates[i] > 2 + 2 * uncertainty]
    print("\nNumerical illustration from the supplied indexed zeta table.")
    print("Indices with both adjacent gaps > 2 and with a unit boundary margin:")
    print(" ", ", ".join(map(str, isolated)))
    print(f"Assuming the table is complete with errors <= {uncertainty},")
    print(f"each sign of the raw centered second difference has mass >= {2 * len(isolated)}")
    print("in [27,183], simultaneously for all 0 < h <= 1. Each isolated")
    print("ordinate contributes +1, -2, +1 at its three translated positions.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zero-table", action="store_true",
                        help="Also check isolated atoms in the numerical zeta table.")
    args = parser.parse_args()
    main()
    if args.zero_table:
        zero_table_diagnostic()
