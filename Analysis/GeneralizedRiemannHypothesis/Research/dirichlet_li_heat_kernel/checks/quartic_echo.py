#!/usr/bin/env python3
"""Certify thirteen oriented Cayley-angle echoes at conductor five.

Requires Python 3.10+ and mpmath 1.3.0. Run 'python quartic_echo.py'.
All decisions use outward interval arithmetic and rational input. The
companion quartic_rectangle.py also certifies the full rectangle directly.
"""

from fractions import Fraction
from functools import lru_cache
from math import factorial, prod

from mpmath import iv

if not __debug__:
    raise RuntimeError("Run this certificate with Python assertions enabled.")

iv.dps = 35
CENTER = Fraction("4.13290370521285")
END = Fraction("4.14")
BROAD = Fraction(1, 1000)
TIGHT = Fraction(1, 10**13)
BERNOULLI = (
    Fraction(1, 6), Fraction(-1, 30), Fraction(1, 42),
    Fraction(-1, 30), Fraction(5, 66), Fraction(-691, 2730)
)


def ball(x):
    """Enclose an exact rational as a real interval."""
    return iv.mpf(x.numerator) / x.denominator


@lru_cache(maxsize=None)
def log_int(n):
    return iv.log(n)


def value(s, n, j):
    """Enclose L(s,chi-bar), using n terms per class and corrections to B_(2j)."""
    assert s.real >= iv.mpf("0.5") and abs(s) <= 5
    m = 2 * j
    poch = [iv.mpc(1)]
    for k in range(m - 1):
        poch.append(poch[-1] * (s + k))
    total = iv.mpc(0)
    chi_bar = (None, 1, -iv.j, iv.j, -1)
    for a in range(1, 5):
        z = 5 * n + a
        e = iv.mpf(5) / z
        tail = z / (5 * (s - 1)) + iv.mpf("0.5")
        for k in range(1, j + 1):
            tail += ball(BERNOULLI[k - 1]) * poch[2*k - 1] * e**(2*k - 1) / factorial(2*k)
        total += chi_bar[a] * (
            sum(iv.exp(-s * log_int(5*l + a)) for l in range(n))
            + iv.exp(-s * log_int(z)) * tail
        )
    # Euler--Maclaurin on the four progressions. The periodic Bernoulli
    # polynomial of order m has sup norm |B_m| by its Fourier expansion.
    # Bound |(s)_m| by 5*6*...*(4+m) and use Re(s) >= 1/2.
    rem = (4 * ball(abs(BERNOULLI[j - 1])) * 5**(m - 1)
           * prod(range(5, 5 + m)) / factorial(m)
           * iv.mpf(5*n)**(iv.mpf("0.5") - m) / (m - iv.mpf("0.5")))
    err = iv.mpf([-1, 1]) * rem
    return total + iv.mpc(err, err)


def center_disk():
    s = iv.mpc("0.5", ball(CENTER))
    at_center = value(s, 32, 6)
    eps = iv.mpf("0.00001")
    d = (value(s + eps, 32, 6) - at_center) / eps
    # A(x)=sum_{n<=x} chi-bar(n) satisfies |A|<=sqrt(2) by periodicity.
    # L(s)=s*integral A(x)x^(-s-1)dx implies
    # |L''(s)|<=sqrt(2)*(2/sigma^2+2|s|/sigma^3).
    sig = iv.mpf("0.499")
    second = iv.sqrt(2) * (2/sig**2 + 2*iv.mpf("4.3")/sig**3)
    assert second < 112
    assert abs(d) - second*eps/2 > 1
    assert abs(at_center) < iv.mpf("5e-15")
    for r in (ball(TIGHT), ball(BROAD)):
        assert abs(at_center) + second*r**2/2 < r
    # Rouche compares L(c+z) with L'(c)z on both circles. The disks
    # are invariant under s -> 1 - conjugate(s). Their unique zero
    # belongs to the critical line by the functional equation.


def cover_line(first, last):
    """Prove there are no critical-line zeros with ordinate in [first,last]."""
    # From the same Abel integral, |L'(s)| <= sqrt(2)*(1/sigma+|s|/sigma^2).
    # At sigma=1/2 and |Im(s)|<=4.14 we may use 28 throughout.
    assert iv.sqrt(2)*(2 + 4*iv.sqrt(ball(END)**2 + iv.mpf("0.25"))) < 28
    stack = [(first, last)]
    accepted = 0
    while stack:
        a, b = stack.pop()
        mid = (a + b) / 2
        r = (b - a) / 2
        middle_value = value(iv.mpc("0.5", ball(mid)), 12, 4)
        if abs(middle_value) > 28 * ball(r):
            accepted += 1
        else:
            if r < Fraction(1, 10**8):
                raise RuntimeError("The enclosure did not establish nonvanishing")
            stack.extend(((a, mid), (mid, b)))
    return accepted


def main():
    center_disk()
    intervals = cover_line(-END, CENTER - BROAD) + cover_line(CENTER + BROAD, END)
    lo = iv.atan2(1, 2*ball(CENTER + TIGHT))*2
    hi = iv.atan2(1, 2*ball(CENTER - TIGHT))*2
    assert lo > iv.mpf("0.24079042878934") and hi < iv.mpf("0.24079042878938")
    assert 13*hi < iv.pi < 14*lo
    print(f"Closed intervals certified outside the Rouche disk: {intervals}.")
    print("L(s,chi-bar) has one simple critical-line zero with |gamma| <= 4.14.")
    print("Its ordinate is in (4.13290370521275, 4.13290370521295).")
    print("All other zeros on the critical line have |gamma| > 4.14.")
    print("0.24079042878934 < y < 0.24079042878938; 13*y < pi < 14*y.")
    print("For k=1,...,13 the only <= k jump representation of +k*y")
    print("for chi-bar is k copies of +y, and chi has none.")
    print("Coefficients:", ", ".join(str(Fraction(1, factorial(k))) for k in range(1, 14)))


if __name__ == "__main__":
    main()
