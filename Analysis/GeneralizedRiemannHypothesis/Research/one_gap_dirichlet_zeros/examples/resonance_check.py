"""Certify a finite four-pole illustration of the resonant displacement law.

Run with Python 3.9+. Only positive integers and fractions are used in the
sign tests, scaled displacements, and the displayed bounds.
"""

from fractions import Fraction
from math import isqrt


def balance_sign(numerator, denominator, power, exterior):
    """Sign at x=numerator/denominator after clearing positive factors."""
    left, right = denominator + numerator, denominator - numerator
    lp, rp = left**power, right**power
    inner = 4 * rp - lp
    if not exterior:
        return (inner > 0) - (inner < 0)
    outer_left = (2 * denominator + numerator)**power
    outer_right = (2 * denominator - numerator)**power
    total = inner * outer_left * outer_right + (2 * outer_right - outer_left) * lp * rp
    return (total > 0) - (total < 0)


def bracket(power, exterior, bits):
    """Return adjacent dyadics bracketing the unique zero in [0, 1/2]."""
    denominator = 2**bits
    lo, hi = 0, denominator // 2
    assert balance_sign(lo, denominator, power, exterior) > 0
    assert balance_sign(hi, denominator, power, exterior) < 0
    while hi - lo > 1:
        mid = (lo + hi) // 2
        sign = balance_sign(mid, denominator, power, exterior)
        if sign == 0:
            return mid, mid, denominator
        if sign > 0:
            lo = mid
        else:
            hi = mid
    assert balance_sign(lo, denominator, power, exterior) > 0
    assert balance_sign(hi, denominator, power, exterior) < 0
    return lo, hi, denominator


def decimal_interval(lo, hi, places):
    """Format an interval with outward rounding for nonnegative endpoints."""
    scale = 10**places
    lower = (lo.numerator * scale) // lo.denominator
    upper = -((-hi.numerator * scale) // hi.denominator)

    def display(number):
        return f"{number // scale}.{number % scale:0{places}d}"

    return f"[{display(lower)}, {display(upper)}]"


def constant_bracket():
    """log(2) = 2 atanh(1/3); bound its positive tail by a geometric series."""
    terms = 25
    log_lo = sum(Fraction(2, (2*j + 1) * 3**(2*j + 1)) for j in range(terms))
    first_tail = Fraction(2, (2*terms + 1) * 3**(2*terms + 1))
    log_hi = log_lo + first_tail * Fraction(9, 8)
    scale = 10**24
    root_lo = isqrt(2 * scale**2)
    return (Fraction(root_lo, scale) * log_lo**3 / 16,
            Fraction(root_lo + 1, scale) * log_hi**3 / 16)


def main():
    print("Weights at -2,-1,+1,+2: 2,4,1,1")
    print("y_p uses only the two inner poles; x_p uses all four.")
    print("Root intervals below are [numerator, numerator+1] / 2^bits.")
    for p in (15, 31, 63, 127):
        bits = p + 3*p.bit_length() + 45
        xlo, xhi, den = bracket(p, True, bits)
        ylo, yhi, yden = bracket(p, False, bits)
        assert den == yden and yhi < xlo
        multiplier = Fraction(p**3 * 2**p, den)
        difference = ((xlo - yhi) * multiplier, (xhi - ylo) * multiplier)
        print(f"p={p:3d} bits={bits:3d} x={xlo} y={ylo}")
        print("    scaled displacement", decimal_interval(*difference, 11))
    print("sqrt(2)*log(2)^3/16", decimal_interval(*constant_bracket(), 11))


if __name__ == "__main__":
    main()
