#!/usr/bin/env python3
"""Exact certificate for the sharp N=2 Euler kernel maximum.

Python standard library only. No floating-point arithmetic is used.
Run: python verify_kernel_algebra.py [output.json]
"""
from fractions import Fraction as F
from math import comb, gcd, lcm
from functools import reduce
from pathlib import Path
import hashlib
import json
import sys


# Univariate polynomials, coefficients in increasing order.
def trim(a):
    a = [F(x) for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a or [F(0)]


def padd(a, b):
    c = [F(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return trim(c)


def pneg(a):
    return [-x for x in a]


def psub(a, b):
    return padd(a, pneg(b))


def pscale(a, c):
    return trim([F(c) * x for x in a])


def pmul(a, b):
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return trim(c)


def ppow(a, n):
    out = [F(1)]
    while n:
        if n & 1:
            out = pmul(out, a)
        a = pmul(a, a)
        n >>= 1
    return out


def pdivmod(a, b):
    a, b = trim(a), trim(b)
    assert b != [0]
    if len(a) < len(b):
        return [F(0)], a
    q = [F(0)] * (len(a) - len(b) + 1)
    while a != [0] and len(a) >= len(b):
        k, c = len(a) - len(b), a[-1] / b[-1]
        q[k] = c
        a = psub(a, [F(0)] * k + pscale(b, c))
    return trim(q), trim(a)


def pexactdiv(a, b):
    q, r = pdivmod(a, b)
    assert r == [0], ("nonexact Bareiss division", r)
    return q


def pmod(a, b):
    return pdivmod(a, b)[1]


def peval(a, x):
    out = F(0)
    for c in reversed(a):
        out = out * x + c
    return out


def pderiv(a):
    return trim([i * a[i] for i in range(1, len(a))])


def det_bareiss(matrix):
    """Fraction-free polynomial determinant with exact divisions."""
    a = [[trim(v) for v in row] for row in matrix]
    n, sign, previous = len(a), 1, [F(1)]
    for k in range(n - 1):
        if a[k][k] == [0]:
            row = next((r for r in range(k + 1, n) if a[r][k] != [0]), None)
            if row is None:
                return [F(0)]
            a[k], a[row] = a[row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = pexactdiv(
                    psub(pmul(pivot, a[i][j]), pmul(a[i][k], a[k][j])),
                    previous,
                )
            a[i][k] = [F(0)]
        previous = pivot
    return pscale(a[-1][-1], sign)


def resultant(a, b):
    """Resultant in outer variable; each coefficient is a polynomial."""
    m, n = len(a) - 1, len(b) - 1
    matrix = [[[F(0)] for _ in range(m + n)] for _ in range(m + n)]
    for row in range(n):
        for j, c in enumerate(reversed(a)):
            matrix[row][row + j] = c
    for row in range(m):
        for j, c in enumerate(reversed(b)):
            matrix[n + row][row + j] = c
    return det_bareiss(matrix)


# Bivariate polynomials in p,y.
def bclean(a):
    return {k: F(v) for k, v in a.items() if v}


def badd(*args):
    out = {}
    for a in args:
        for k, v in a.items():
            out[k] = out.get(k, F(0)) + v
    return bclean(out)


def bscale(a, c):
    return bclean({k: F(c) * v for k, v in a.items()})


def bmul(*args):
    out = {(0, 0): F(1)}
    for a in args:
        new = {}
        for (i, j), x in out.items():
            for (k, l), y in a.items():
                key = (i + k, j + l)
                new[key] = new.get(key, F(0)) + x * y
        out = bclean(new)
    return out


def bderiv(a, axis):
    out = {}
    for degree, c in a.items():
        if degree[axis]:
            k = list(degree)
            k[axis] -= 1
            out[tuple(k)] = c * degree[axis]
    return bclean(out)


def bfrom_outer(a):
    return bclean({(i, j): c for i, poly in enumerate(a) for j, c in enumerate(poly)})


# Exact finite-field irreducibility for prime degree seven.
def mt(a, p):
    a = [int(x) % p for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a or [0]


def mmul(a, b, p):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] = (c[i + j] + x * y) % p
    return mt(c, p)


def mdivmod(a, b, p):
    a, b = mt(a, p), mt(b, p)
    assert b != [0]
    q = [0] * max(1, len(a) - len(b) + 1)
    while a != [0] and len(a) >= len(b):
        k = len(a) - len(b)
        c = a[-1] * pow(b[-1], -1, p) % p
        q[k] = c
        for j, x in enumerate(b):
            a[k + j] = (a[k + j] - c * x) % p
        a = mt(a, p)
    return mt(q, p), a


def mpow(a, n, modulus, p):
    out = [1]
    while n:
        if n & 1:
            out = mdivmod(mmul(out, a, p), modulus, p)[1]
        a = mdivmod(mmul(a, a, p), modulus, p)[1]
        n >>= 1
    return out


def mgcd(a, b, p):
    while b != [0]:
        a, b = b, mdivmod(a, b, p)[1]
    inverse = pow(a[-1], -1, p)
    return mt([inverse * x for x in a], p)


def irreducible_degree_seven(poly, p=5):
    f = mt(poly, p)
    assert len(f) == 8
    inverse = pow(f[-1], -1, p)
    f = mt([inverse * x for x in f], p)
    xp = [0, 1]
    residues = []
    for _ in range(7):
        xp = mpow(xp, p, f, p)
        residues.append(xp)
    assert xp == [0, 1]  # x^(5^7)−x divisible by f.
    x5_minus_x = [0, -1, 0, 0, 0, 1]
    g = mgcd(f, mt(x5_minus_x, p), p)
    assert g == [1]      # No degree-one irreducible factor.
    # Irreducible factor degrees must divide seven; excluding one forces seven.
    return {"prime": p, "monic_polynomial": f,
            "frobenius_residues": residues, "linear_factor_gcd": g}


# Rational intervals; all operations enclose with exact endpoints.
class I:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = F(lo), F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = other if isinstance(other, I) else I(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other if isinstance(other, I) else -F(other))

    def __rsub__(self, other):
        return (-self) + other

    def __mul__(self, other):
        other = other if isinstance(other, I) else I(other)
        values = [self.lo * other.lo, self.lo * other.hi,
                  self.hi * other.lo, self.hi * other.hi]
        return I(min(values), max(values))

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.lo * self.hi > 0
        return I(1 / self.hi, 1 / self.lo)

    def __truediv__(self, other):
        other = other if isinstance(other, I) else I(other)
        return self * other.reciprocal()


def ieval(poly, x):
    out = I(0)
    for c in reversed(poly):
        out = out * x + c
    return out


def isolate(poly, lo, hi, steps=180, increasing=True):
    lo, hi = F(lo), F(hi)
    direction = 1 if increasing else -1
    assert direction * peval(poly, lo) < 0 < direction * peval(poly, hi)
    for _ in range(steps):
        mid = (lo + hi) / 2
        val = peval(poly, mid)
        assert val != 0  # Both degree-seven polynomials are irreducible.
        if direction * val < 0:
            lo = mid
        else:
            hi = mid
    return I(lo, hi)


def decimal_bound(x, digits, upward):
    scale = 10 ** digits
    q = (x.numerator * scale) // x.denominator
    if upward and F(q, scale) < x:
        q += 1
    sign = "-" if q < 0 else ""
    q = abs(q)
    return f"{sign}{q // scale}.{q % scale:0{digits}d}"


def rat(x):
    x = F(x)
    return f"{x.numerator}/{x.denominator}"


def interval_json(x, digits=40):
    return {"lower": rat(x.lo), "upper": rat(x.hi),
            "decimal_lower": decimal_bound(x.lo, digits, False),
            "decimal_upper": decimal_bound(x.hi, digits, True)}


def bernstein_on_unit_interval(poly):
    n = len(poly) - 1
    return [
        sum((poly[k] * F(comb(j, k), comb(n, k)) for k in range(j + 1)), F(0))
        for j in range(n + 1)
    ]


def shift_by_one(poly):
    out = [F(0)] * len(poly)
    for i, c in enumerate(poly):
        for j in range(i + 1):
            out[j] += c * comb(i, j)
    return trim(out)


def main():
    # Increasing-order polynomial definitions.
    P = [[-3], [2, 0, 2], [1, 0, 8, 0, 1],
         [0, 0, 2, 0, 2], [0, 0, 0, 0, 1]]
    Q = [[-3], [1, 8, 6], [0, 0, 2, 0, 1], [0, 0, 0, 0, 1]]
    P, Q = [[trim(a) for a in family] for family in (P, Q)]
    R = trim([-4, 0, 59, 17, -10, -2, 3, 1])
    D = trim([4, 36, 17, -6, -2, 2, 1])
    Mpoly = trim([20736, 99072, -66352, -32216, -4523, 2538, -416, 32])

    one, p, y = {(0, 0): F(1)}, {(1, 0): F(1)}, {(0, 1): F(1)}
    yy = bmul(y, y)
    op, oy = badd(one, p), badd(one, y)
    opyy = badd(one, bmul(p, yy))
    numerator = bmul(p, oy, badd(bscale(one, 3), bscale(p, -1),
                               bscale(bmul(p, yy), -1),
                               bscale(bmul(p, p, yy), -1)))
    denominator = bmul(op, opyy)
    derivative_p = badd(bmul(bderiv(numerator, 0), denominator),
                        bscale(bmul(numerator, bderiv(denominator, 0)), -1))
    derivative_y = badd(bmul(bderiv(numerator, 1), denominator),
                        bscale(bmul(numerator, bderiv(denominator, 1)), -1))
    assert derivative_p == bscale(bmul(oy, bfrom_outer(P)), -1)
    assert derivative_y == bscale(bmul(p, op, bfrom_outer(Q)), -1)

    res = resultant(P, Q)
    expected_res = pscale(pmul([0] * 10 + [1, 1], R), -192)
    assert res == expected_res

    # P(12/D,y)D^4 and Q(12/D,y)D^3 vanish modulo R.
    substitution_remainders = []
    for family in (P, Q):
        degree = len(family) - 1
        value = [F(0)]
        for j, coefficient in enumerate(family):
            value = padd(value, pscale(pmul(coefficient, ppow(D, degree - j)), 12 ** j))
        remainder = pmod(value, R)
        assert remainder == [0]
        substitution_remainders.append(remainder)

    # Rational value K2(12/D,y) = value_num/value_den.
    y2 = [0, 0, 1]
    value_num = pscale(
        pmul([1, 1], psub(psub(pscale(ppow(D, 2), 3),
                               pscale(pmul(D, [1, 0, 1]), 12)),
                         pscale(y2, 144))), 12)
    value_den = pmul(D, pmul(padd(D, [12]), padd(D, pscale(y2, 12))))

    # Norm from Q[y]/(R): determinant of multiplication by m*den−num.
    norm_matrix = [[[F(0)] for _ in range(7)] for _ in range(7)]
    for column in range(7):
        monomial = [F(0)] * column + [F(1)]
        nc = pmod(pmul(value_num, monomial), R)
        dc = pmod(pmul(value_den, monomial), R)
        for row in range(7):
            norm_matrix[row][column] = trim([
                -nc[row] if row < len(nc) else 0,
                dc[row] if row < len(dc) else 0,
            ])
    norm = det_bareiss(norm_matrix)
    multiplier = norm[-1] / Mpoly[-1]
    assert multiplier != 0 and norm == pscale(Mpoly, multiplier)

    irred_R = irreducible_degree_seven(R)
    irred_M = irreducible_degree_seven(Mpoly)

    # Exact derivative certificate: R'(y)>68y for 0<y<1.
    assert pderiv(R) == trim([0, 118, 51, -40, -10, 18, 7])
    # Positive pieces 7y^5+18y^4+51y plus 118−10y^3−40y^2 exceed 68.

    # Unique root of Mpoly in (1,2), certified by negative Bernstein derivative.
    derivative_bernstein = bernstein_on_unit_interval(shift_by_one(pderiv(Mpoly)))
    assert all(c < 0 for c in derivative_bernstein)
    assert peval(Mpoly, 1) == 18871 and peval(Mpoly, 2) == -317936

    y_interval = isolate(R, 0, 1, increasing=True)
    D_interval = ieval(D, y_interval)
    assert D_interval.lo > 0
    p_interval = I(12) / D_interval
    assert 0 < p_interval.lo < p_interval.hi < 1
    direct_M = ieval(value_num, y_interval) / ieval(value_den, y_interval)
    assert 1 < direct_M.lo < direct_M.hi < 2
    polynomial_M = isolate(Mpoly, 1, 2, increasing=False)
    maximum_interval = I(max(direct_M.lo, polynomial_M.lo),
                         min(direct_M.hi, polynomial_M.hi))

    # Several short rational boundary checks from the analytic proof.
    assert peval(R, 0) == -4 and peval(R, 1) == 64
    sample_p, sample_y = F(3, 4), F(1, 4)
    sample = (sample_p * (1 + sample_y) *
              (3 - sample_p - sample_p * sample_y ** 2 - sample_p ** 2 * sample_y ** 2) /
              ((1 + sample_p) * (1 + sample_p * sample_y ** 2)))
    assert sample == F(8325, 7504) and sample > 1

    report = {
        "status": "all exact checks passed",
        "arithmetic": "Python standard-library integers and fractions; no floating point",
        "polynomial_coefficient_order": "ascending",
        "derivative_identities": {"p": True, "y": True},
        "sylvester_resultant_coefficients": [rat(c) for c in res],
        "substitution_remainders_mod_R": [[rat(c) for c in r]
                                        for r in substitution_remainders],
        "maximum_polynomial": [rat(c) for c in Mpoly],
        "norm_multiplier": rat(multiplier),
        "irreducibility_R": irred_R,
        "irreducibility_maximum": irred_M,
        "R_endpoint_values": [-4, 64],
        "maximum_polynomial_endpoint_values": [18871, -317936],
        "maximum_derivative_Bernstein_on_1_2": [rat(c) for c in derivative_bernstein],
        "rational_interior_sample": rat(sample),
        "y2": interval_json(y_interval),
        "p2": interval_json(p_interval),
        "M2_via_kernel": interval_json(direct_M),
        "M2": interval_json(maximum_interval),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    output = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "output": str(output),
                      "M2": report["M2"],
                      "y2": report["y2"], "p2": report["p2"]}, indent=2))


if __name__ == "__main__":
    main()

