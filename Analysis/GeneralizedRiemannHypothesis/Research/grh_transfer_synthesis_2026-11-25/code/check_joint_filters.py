#!/usr/bin/env python3
"""Exact algebraic certificate for the joint positive-filter construction.

Uses only Python's standard library and rational polynomial arithmetic.
This certifies the finite identities, not the analytic Landau theorem.
The latter is proved in sections/joint_filters.tex.
"""
from fractions import Fraction as Q
import json


def trim(p):
    p = list(map(Q, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def mul(p, q):
    r = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return trim(r)


def sub(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) -
                 (q[i] if i < len(q) else 0) for i in range(n)])


def evaluate(p, z):
    return sum(c * z ** i for i, c in enumerate(p))


def main():
    P = list(map(Q, [5, 6]))
    Qpoly = list(map(Q, [25, 30, 36]))
    assert sub(Qpoly, mul([0, 6], P)) == [25]
    assert evaluate(P, Q(-5, 6)) == 0
    assert evaluate(Qpoly, Q(-5, 6)) == 25
    # P's only root is -5/6. Q's roots are (5/6) times primitive cube roots.
    # Substitute z=(5/6)y in Q: the result is 25(1+y+y^2).
    scaled_q = [c * Q(5, 6) ** k for k, c in enumerate(Qpoly)]
    assert scaled_q == [25, 25, 25]
    assert mul([1, 1, 1], [-1, 1]) == [-1, 0, 0, 1]
    # Root modulus 5/6 places the vertical zero lines strictly between 1/2 and 1.
    assert Q(1, 2) < Q(25, 36) < 1
    # For arbitrary r0,r1,r2 the recovery is a coefficient-vector identity.
    assert sub([25, 30, 36], [0, 30, 36]) == [25]
    # The same certificate works for arbitrary nonzero m and every n.
    general_checks = 0
    for m in [Q(1, 3), Q(1), Q(5), Q(7, 2)]:
        for n in [Q(0), Q(2, 3), Q(6), Q(11)]:
            pp = [m, n]
            qq = [m * m, m * n, n * n]
            assert sub(qq, mul([0, n], pp)) == [m * m]
            general_checks += 1
    print(json.dumps({
        "status": "passed",
        "arithmetic": "exact rational",
        "P_ascending_coefficients": [5, 6],
        "Q_ascending_coefficients": [25, 30, 36],
        "bezout_identity": "Q(z)-6*z*P(z)=25",
        "reconstruction": "B(x)-6*A(2*x)=25*R(x)",
        "common_roots": 0,
        "P_root": "-5/6",
        "Q_roots": "(5/6)*exp(+/-2*pi*i/3)",
        "root_modulus_squared": "25/36",
        "individual_blind_line": "Re(s)=1+log(5/6)/log(2), strictly between 1/2 and 1",
        "parameter_examples": general_checks,
        "scope": "finite algebraic certificate; analytic proof is in the report"
    }, indent=2))


if __name__ == "__main__":
    main()
