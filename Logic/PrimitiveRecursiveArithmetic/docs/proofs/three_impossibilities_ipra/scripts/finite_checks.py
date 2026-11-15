#!/usr/bin/env python3
"""Exact finite checks supporting the iPRA construction-impossibility report.

These checks are diagnostics, not a proof of the full theorem.  They use only
Python's standard library and exact integers/Fractions.
"""

from __future__ import annotations

from fractions import Fraction
from math import factorial
from typing import Iterable, List, Sequence, Tuple

Poly = List[int]  # coefficient order: constant term first
CFrac = Tuple[Fraction, Fraction]


def trim(p: Sequence[int]) -> Poly:
    q = list(p)
    while len(q) > 1 and q[-1] == 0:
        q.pop()
    return q


def padd(a: Sequence[int], b: Sequence[int]) -> Poly:
    n = max(len(a), len(b))
    out = [0] * n
    for i in range(n):
        out[i] = (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
    return trim(out)


def pmul(a: Sequence[int], b: Sequence[int]) -> Poly:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def ppow(a: Sequence[int], n: int) -> Poly:
    out: Poly = [1]
    base = list(a)
    while n:
        if n & 1:
            out = pmul(out, base)
        base = pmul(base, base)
        n //= 2
    return out


def pderiv(a: Sequence[int], j: int = 1) -> Poly:
    out = list(a)
    for _ in range(j):
        if len(out) <= 1:
            return [0]
        out = [k * out[k] for k in range(1, len(out))]
    return trim(out)


def peval(a: Sequence[int], x: Fraction | int) -> Fraction:
    y = Fraction(0)
    xx = Fraction(x)
    for c in reversed(a):
        y = y * xx + c
    return y


def cadd(z: CFrac, w: CFrac) -> CFrac:
    return (z[0] + w[0], z[1] + w[1])


def cmul(z: CFrac, w: CFrac) -> CFrac:
    return (z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def cinv(z: CFrac) -> CFrac:
    n = z[0] * z[0] + z[1] * z[1]
    assert n != 0
    return (z[0] / n, -z[1] / n)


def cpow(z: CFrac, n: int) -> CFrac:
    out: CFrac = (Fraction(1), Fraction(0))
    base = z
    while n:
        if n & 1:
            out = cmul(out, base)
        base = cmul(base, base)
        n //= 2
    return out


def exp_two_i_atan_rational(x: Fraction) -> CFrac:
    # (1 + i x)/(1 - i x) = ((1-x^2) + 2ix)/(1+x^2)
    den = 1 + x * x
    return ((1 - x * x) / den, (2 * x) / den)


def rational_root_candidates_monic(constant: int) -> list[int]:
    if constant == 0:
        return [0]
    n = abs(constant)
    out: list[int] = []
    for d in range(1, n + 1):
        if n % d == 0:
            out.extend([d, -d])
    return sorted(set(out))


def check_cubics() -> None:
    cube = [-2, 0, 0, 1]
    trisect = [-1, -3, 0, 1]
    for name, p in [("X^3-2", cube), ("X^3-3X-1", trisect)]:
        candidates = rational_root_candidates_monic(p[0])
        vals = {r: peval(p, r) for r in candidates}
        assert all(v != 0 for v in vals.values())
        print(f"PASS cubic irreducibility diagnostic: {name}; candidates {vals}")


def check_triple_angle_rescaling() -> None:
    # If t=2x, then 4x^3-3x=1/2 iff t^3-3t-1=0.
    for x in [Fraction(-3, 2), Fraction(-1, 3), Fraction(0), Fraction(2, 5), Fraction(7, 6)]:
        t = 2 * x
        lhs = 2 * (4 * x**3 - 3 * x - Fraction(1, 2))
        rhs = t**3 - 3 * t - 1
        assert lhs == rhs
    print("PASS exact triple-angle rescaling identity")


def check_machin_identity() -> None:
    a = Fraction(1, 5)
    b = Fraction(1, 239)

    # Tangent calculation.
    tan2a = 2 * a / (1 - a * a)
    tan4a = 2 * tan2a / (1 - tan2a * tan2a)
    tan_theta = (tan4a - b) / (1 + tan4a * b)
    assert tan2a == Fraction(5, 12)
    assert tan4a == Fraction(120, 119)
    assert tan_theta == 1

    # Exact complex form: exp(2 i (4 atan(1/5)-atan(1/239))) = i.
    za = exp_two_i_atan_rational(a)
    zb = exp_two_i_atan_rational(b)
    ztheta = cmul(cpow(za, 4), cinv(zb))
    assert ztheta == (Fraction(0), Fraction(1))
    print("PASS Machin tangent identity and exact rational complex identity")


def sum_polys(polys: Iterable[Sequence[int]]) -> Poly:
    out: Poly = [0]
    for p in polys:
        out = padd(out, p)
    return out


def divide_poly_coeffs_exact(p: Sequence[int], n: int) -> Poly:
    assert n != 0
    assert all(c % n == 0 for c in p)
    return trim([c // n for c in p])


def check_hermite_for(F: Poly, p: int) -> None:
    assert p > abs(F[0]) and p >= 2
    d = len(trim(F)) - 1
    h = [0] * (p - 1) + ppow(F, p)
    D = len(h) - 1
    derivs = [pderiv(h, j) for j in range(D + 1)]
    A = sum_polys(derivs)

    n_num = A[0]
    n_den = factorial(p - 1)
    assert n_num % n_den == 0
    n_p = n_num // n_den
    assert n_p % p == pow(F[0], p, p)
    assert n_p % p != 0

    p_fact = factorial(p)
    high_derivs = derivs[p:]
    assert all(all(c % p_fact == 0 for c in q) for q in high_derivs)
    g = sum_polys(divide_poly_coeffs_exact(q, p_fact) for q in high_derivs)
    assert len(g) - 1 <= p * d - 1

    # Check A(r) = (p-1)! p g(r) at the two exact roots of 2X^2-3X+1.
    if F == [1, -3, 2]:
        for r in [Fraction(1), Fraction(1, 2)]:
            assert peval(A, r) == factorial(p - 1) * p * peval(g, r)

    print(
        "PASS Hermite divisibility: "
        f"F={F}, p={p}, deg(h)={D}, deg(g)={len(g)-1}, n_p mod p={n_p % p}"
    )


def check_root_sum_integrality() -> None:
    # F=2X^2-3X+1, roots 1 and 1/2, leading coefficient ell=2.
    roots = [Fraction(1), Fraction(1, 2)]
    ell = 2
    tests = [
        ([3], 0),
        ([1, -4], 1),
        ([2, 0, 5], 2),
        ([-7, 3, -2, 1], 5),
    ]
    for g, m in tests:
        assert m >= len(trim(g)) - 1
        value = Fraction(ell**m) * sum(peval(g, r) for r in roots)
        assert value.denominator == 1
    print("PASS scaled root-sum integrality examples")


def check_factorial_threshold() -> None:
    for A, d in [(1, 1), (2, 3), (3, 1), (4, 9), (7, 5), (10, 20)]:
        q = max(1, 2 * A * A, d)
        T = 2 * q
        for p in range(T, T + 12):
            assert d * (A**p) < factorial(p - 1)
        print(f"PASS factorial threshold: A={A}, d={d}, T={T}")


def check_subset_sum_example() -> None:
    # For roots theta=(sqrt(2),-sqrt(2)), subset sums are 0,+s,-s,0.
    # Their polynomial is Y^2(Y^2-2)=Y^4-2Y^2.
    Q = [0, 0, -2, 0, 1]
    assert Q == pmul([0, 0, 1], [-2, 0, 1])
    print("PASS symmetric subset-sum polynomial example: Y^2(Y^2-2)")


def main() -> None:
    check_cubics()
    check_triple_angle_rescaling()
    check_machin_identity()
    check_subset_sum_example()
    check_root_sum_integrality()
    check_hermite_for([1, -3, 2], 5)
    check_hermite_for([1, -3, 2], 7)
    check_hermite_for([-2, 0, 1], 5)
    check_factorial_threshold()
    print("ALL FINITE DIAGNOSTIC CHECKS PASSED")


if __name__ == "__main__":
    main()
