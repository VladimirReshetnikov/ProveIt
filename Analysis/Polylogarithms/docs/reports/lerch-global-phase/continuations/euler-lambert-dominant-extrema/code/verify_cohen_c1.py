#!/usr/bin/env python3
"""Exact coefficient audit for the first two extreme-root corrections.

Standard library only: sparse multivariate polynomials over Fraction.
This verifies finite symbolic algebra, not the analytic saddle error bound.
Run: python verify_cohen_c1.py [output.json]
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import sys


NAMES = ("z", "c", "s2", "s3", "s4", "s5", "kappa", "eta")
ZERO = (0,) * len(NAMES)


class P:
    def __init__(self, data=0):
        if isinstance(data, P):
            self.d = dict(data.d)
        elif isinstance(data, dict):
            self.d = {m: F(a) for m, a in data.items() if a}
        else:
            self.d = {ZERO: F(data)} if data else {}

    def __add__(self, other):
        out = dict(self.d)
        for m, a in P(other).d.items():
            out[m] = out.get(m, F(0)) + a
        return P(out)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -a for m, a in self.d.items()})

    def __sub__(self, other):
        return self + (-P(other))

    def __rsub__(self, other):
        return P(other) + (-self)

    def __mul__(self, other):
        out = {}
        for m, a in self.d.items():
            for n, b in P(other).d.items():
                degree = tuple(i + j for i, j in zip(m, n))
                out[degree] = out.get(degree, F(0)) + a * b
        return P(out)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        return self * (F(1) / F(scalar))

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        out, a = P(1), self
        while n:
            if n & 1:
                out = out * a
            a = a * a
            n >>= 1
        return out

    def __eq__(self, other):
        return self.d == P(other).d

    def derivative(self, axis=0, order=1):
        out = self
        for _ in range(order):
            terms = {}
            for m, a in out.d.items():
                if m[axis]:
                    degree = list(m)
                    degree[axis] -= 1
                    terms[tuple(degree)] = a * m[axis]
            out = P(terms)
        return out

    def coefficient(self, axis, degree):
        out = {}
        for m, a in self.d.items():
            if m[axis] == degree:
                key = list(m)
                key[axis] = 0
                out[tuple(key)] = a
        return P(out)

    def truncate(self, axis, degree):
        return P({m: a for m, a in self.d.items() if m[axis] <= degree})

    def serialize(self):
        rows = []
        for m, a in sorted(self.d.items()):
            rows.append({
                "coefficient": str(a),
                "monomial": {NAMES[i]: power for i, power in enumerate(m) if power},
            })
        return rows


def variable(i):
    m = list(ZERO)
    m[i] = 1
    return P({tuple(m): F(1)})


z, c, s2, s3, s4, s5, kappa, eta = [variable(i) for i in range(len(NAMES))]


def at_zero(poly, order=0):
    return poly.derivative(0, order).coefficient(0, 0)


def transform1(poly):
    return -(1 + z)**2 * poly.derivative(0, 2) / 2


def transform2(poly):
    return ((1 + z)**3 * poly.derivative(0, 3) / 3
            + (1 + z)**4 * poly.derivative(0, 4) / 8)


def transform3(poly):
    return (-(1 + z)**4 * poly.derivative(0, 4) / 4
            - (1 + z)**5 * poly.derivative(0, 5) / 6
            - (1 + z)**6 * poly.derivative(0, 6) / 48)


def main():
    moments = []
    for r in range(7):
        moment = P(0)
        for j in range(r + 1):
            falling = P(1)
            for m in range(j):
                falling *= 1 - m * eta
            moment += (-1)**(r - j) * comb(r, j) * falling
        moments.append(moment)
    assert moments[:5] == [P(1), P(0), -eta, 2*eta**2, 3*eta**2 - 6*eta**3]
    assert moments[5].truncate(7, 3) == -20*eta**3
    assert moments[6].truncate(7, 3) == -15*eta**3

    # Normalize g'(1) to 1, which does not affect any zero.
    exponent = c*z - s2*z**2/2 + s3*z**3/3 - s4*z**4/4 + s5*z**5/5
    exp_series, term = P(1), P(1)
    for m in range(1, 6):
        term = (term * exponent / m).truncate(0, 5)
        exp_series += term
    g = z * exp_series
    v = 1 + z
    q1 = v*(v + 1)/2
    q2 = v*(v + 1)*(v + 2)*(3*v + 1)/24

    # Substitute eta = eps/(1+kappa eps), retain eps through degree 3.
    # The omitted q3(v)*g(v) vanishes at v=1 and is irrelevant at this order.
    A1 = q1*g + transform1(g)
    A2 = q2*g + transform1(q1*g) - kappa*transform1(g) + transform2(g)
    A3 = (transform1(q2*g) - kappa*transform1(q1*g)
          + kappa**2*transform1(g) + transform2(q1*g)
          - 2*kappa*transform2(g) + transform3(g))

    # The nearby root is v=1+u1 eps+u2 eps^2+u3 eps^3+O(eps^4).
    u1 = -at_zero(A1)
    u2 = -(c*u1**2 + at_zero(A1, 1)*u1 + at_zero(A2))
    u3 = -(2*c*u1*u2 + (c**2-s2)*u1**3/2 + at_zero(A1, 1)*u2
           + at_zero(A1, 2)*u1**2/2 + at_zero(A2, 1)*u1 + at_zero(A3))
    assert u1 == c
    assert u2 == s2 - s3 + c**2 - c*kappa + F(3, 2)

    # X-log n=(eps^(-1)+kappa)/v.
    C0 = u1**2 - u2 - kappa*u1
    C1 = -u3 + 2*u1*u2 - u1**3 + kappa*(u1**2-u2)
    expected0 = -s2 + s3 - F(3, 2)
    expected1 = (-s2**2 + s2*s3 + kappa*s2 - kappa*s3
                 - 2*s3 + 5*s4 - 3*s5 - F(1, 12))
    assert C0 == expected0
    assert C1 == expected1
    assert all(m[1] == 0 for m in C0.d)  # Euler's constant cancels.
    assert all(m[1] == 0 for m in C1.d)

    report = {
        "status": "all exact rational-polynomial assertions passed",
        "arithmetic": "Python standard library, Fraction, no floating point",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "normalization": "kappa=k-1; c=-gamma; s2=zeta(2); s3=-zeta(3); s4=zeta(4); s5=-zeta(5)",
        "moments": {str(r): p.serialize() for r, p in enumerate(moments)},
        "C0_cumulants": C0.serialize(),
        "C1_cumulants": C1.serialize(),
        "C0": "-3/2-zeta(2)-zeta(3)",
        "C1": "(k-1)*(zeta(2)+zeta(3))+zeta(2)^2-zeta(2)*zeta(3)+2*zeta(3)+3*zeta(5)-1/12",
        "simplification_used": "zeta(4)=(2/5)*zeta(2)^2",
    }
    target = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_suffix(".json")
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "output": str(target)}))


if __name__ == "__main__":
    main()
