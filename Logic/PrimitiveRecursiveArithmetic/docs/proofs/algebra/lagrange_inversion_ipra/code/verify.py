#!/usr/bin/env python3
"""Exact arithmetic checks for the constructive Lagrange-inversion packet.

This is not a proof of the theorems.  It is an independent executable check
of representative finite coefficient identities used in the paper.  All
univariate and multivariate coefficients are fractions.Fraction values.
"""

from __future__ import annotations

from fractions import Fraction as Q
from math import comb, factorial
from typing import Dict, Iterable, List, Sequence, Tuple

Series = List[Q]
MI = Tuple[int, ...]
MV = Dict[MI, Q]


def trim(a: Series, n: int) -> Series:
    return (a + [Q(0)] * (n + 1))[: n + 1]


def add(a: Series, b: Series, n: int) -> Series:
    a, b = trim(a, n), trim(b, n)
    return [a[i] + b[i] for i in range(n + 1)]


def sub(a: Series, b: Series, n: int) -> Series:
    a, b = trim(a, n), trim(b, n)
    return [a[i] - b[i] for i in range(n + 1)]


def scale(c: Q, a: Series, n: int) -> Series:
    a = trim(a, n)
    return [c * x for x in a]


def mul(a: Series, b: Series, n: int) -> Series:
    a, b = trim(a, n), trim(b, n)
    out = [Q(0)] * (n + 1)
    for i in range(n + 1):
        for j in range(n + 1 - i):
            out[i + j] += a[i] * b[j]
    return out


def power(a: Series, k: int, n: int) -> Series:
    out = [Q(1)] + [Q(0)] * n
    base = trim(a, n)
    while k:
        if k & 1:
            out = mul(out, base, n)
        base = mul(base, base, n)
        k //= 2
    return out


def derivative(a: Series, n: int) -> Series:
    a = trim(a, n + 1)
    return [Q(i + 1) * a[i + 1] for i in range(n + 1)]


def compose(a: Series, b: Series, n: int) -> Series:
    """a(b(x)) modulo x^(n+1); requires b(0)=0 for finite dependence."""
    assert not b or b[0] == 0
    out = [Q(0)] * (n + 1)
    p = [Q(1)] + [Q(0)] * n
    aa = trim(a, n)
    for k in range(n + 1):
        out = add(out, scale(aa[k], p, n), n)
        p = mul(p, b, n)
    return out


def reciprocal(a: Series, n: int) -> Series:
    a = trim(a, n)
    assert a[0] != 0
    b = [Q(0)] * (n + 1)
    b[0] = 1 / a[0]
    for m in range(1, n + 1):
        b[m] = -sum(a[k] * b[m - k] for k in range(1, m + 1)) / a[0]
    return b


def fixed_point(phi: Series, n: int) -> Series:
    """Unique g with g=x*phi(g), modulo x^(n+1), by N iterations."""
    x = [Q(0), Q(1)] + [Q(0)] * max(0, n - 1)
    g = [Q(0)] * (n + 1)
    for _ in range(n + 1):
        g = mul(x, compose(phi, g, n), n)
    return g


def compositional_inverse(f: Series, n: int) -> Series:
    """Inverse of f with f(0)=0 and f'(0) nonzero."""
    f = trim(f, n)
    assert f[0] == 0 and f[1] != 0
    # phi(w)=w/f(w)=1/(f(w)/w)
    shifted = [f[i + 1] if i + 1 <= n else Q(0) for i in range(n + 1)]
    phi = reciprocal(shifted, n)
    return fixed_point(phi, n)


def partial_bell(m: int, k: int, xs: Sequence[Q]) -> Q:
    """Exponential partial Bell polynomial B_{m,k}(x_1,...)."""
    total = Q(0)

    def rec(j: int, remaining_count: int, remaining_weight: int, denom: int, prod: Q) -> None:
        nonlocal total
        if j > m:
            if remaining_count == 0 and remaining_weight == 0:
                total += Q(factorial(m), denom) * prod
            return
        max_r = min(remaining_count, remaining_weight // j)
        xj = xs[j - 1] if j - 1 < len(xs) else Q(0)
        for r in range(max_r + 1):
            rec(
                j + 1,
                remaining_count - r,
                remaining_weight - j * r,
                denom * factorial(r) * (factorial(j) ** r),
                prod * (xj ** r),
            )

    rec(1, k, m, 1, Q(1))
    return total


def rising(n: int, k: int) -> int:
    out = 1
    for j in range(k):
        out *= n + j
    return out


def check_univariate_lagrange() -> None:
    nmax = 9
    phi = [Q(2), Q(-1), Q(3, 2), Q(1, 3), Q(-2, 5), Q(7, 11)]
    h = [Q(3), Q(2), Q(-1), Q(5, 4), Q(2, 7), Q(-3, 8)]
    g = fixed_point(phi, nmax)
    hg = compose(h, g, nmax)
    hp = derivative(h, nmax)
    phip = derivative(phi, nmax)
    xphip = [Q(0)] + phip[:nmax]
    for n in range(1, nmax + 1):
        rhs_der = mul(hp, power(phi, n, nmax), nmax)[n - 1] / n
        bracket = sub(phi, xphip, nmax)
        rhs_alt = mul(mul(h, power(phi, n - 1, nmax), nmax), bracket, nmax)[n]
        assert hg[n] == rhs_der == rhs_alt, (n, hg[n], rhs_der, rhs_alt)
    print("PASS univariate Lagrange-Buermann, both coefficient forms, n<=9")


def check_inverse_and_bell() -> None:
    nmax = 8
    # Exponential coefficients f_n for f(w)=sum f_n w^n/n!.
    fexp = [Q(0), Q(2), Q(3), Q(-1), Q(4), Q(5), Q(-7), Q(2), Q(9)]
    f = [fexp[n] / factorial(n) for n in range(nmax + 1)]
    g = compositional_inverse(f, nmax)
    assert compose(f, g, nmax) == [Q(0), Q(1)] + [Q(0)] * (nmax - 1)
    for n in range(2, nmax + 1):
        hats = [fexp[j + 1] / (Q(j + 1) * fexp[1]) for j in range(1, n)]
        bell_sum = sum(
            Q((-1) ** k * rising(n, k)) * partial_bell(n - 1, k, hats)
            for k in range(1, n)
        ) / (fexp[1] ** n)
        assert factorial(n) * g[n] == bell_sum, (n, factorial(n) * g[n], bell_sum)
    print("PASS Bell-polynomial inverse-coefficient formula, n<=8")


def check_algebraic_family() -> None:
    nmax = 24
    for p in range(2, 7):
        # phi=(1-w^(p-1))^-1
        phi = [Q(0)] * (nmax + 1)
        for j in range(0, nmax + 1, p - 1):
            phi[j] = 1
        g = fixed_point(phi, nmax)
        for n in range(1, nmax + 1):
            if (n - 1) % (p - 1):
                expected = Q(0)
            else:
                k = (n - 1) // (p - 1)
                expected = Q(comb(p * k, k), (p - 1) * k + 1)
            assert g[n] == expected, (p, n, g[n], expected)
    print("PASS x^p-x+z coefficient formula, p=2..6 through degree 24")


def check_lambert_w() -> None:
    nmax = 12
    # exp(-w)
    phi = [Q((-1) ** j, factorial(j)) for j in range(nmax + 1)]
    g = fixed_point(phi, nmax)
    for n in range(1, nmax + 1):
        expected = Q((-n) ** (n - 1), factorial(n))
        assert g[n] == expected, (n, g[n], expected)
    expected_head = [Q(0), Q(1), Q(-1), Q(3, 2), Q(-8, 3), Q(125, 24)]
    assert g[:6] == expected_head
    print("PASS Lambert W coefficients (-n)^(n-1)/n!, n<=12")


def check_shifted_lambert() -> None:
    nmax = 10
    # A(u)=u+log(1+u)=2u-u^2/2+u^3/3-...
    a = [Q(0)] * (nmax + 1)
    a[1] = Q(2)
    for n in range(2, nmax + 1):
        a[n] = Q((-1) ** (n + 1), n)
    u = compositional_inverse(a, nmax)
    expected = [
        Q(0), Q(1, 2), Q(1, 16), Q(-1, 192), Q(-1, 3072),
        Q(13, 61440), Q(-47, 1474560),
    ]
    assert u[: len(expected)] == expected, (u[: len(expected)], expected)
    print("PASS shifted Lambert W series through z^6")


def check_catalan() -> None:
    nmax = 15
    phi = [Q(1), Q(2), Q(1)]  # (1+w)^2
    c = fixed_point(phi, nmax)
    for n in range(1, nmax + 1):
        expected = Q(comb(2 * n, n), n + 1)
        assert c[n] == expected
    print("PASS binary-tree/Catalan specialization, n<=15")


def exp_bounds_positive(x: Q, terms: int = 30) -> Tuple[Q, Q]:
    assert x >= 0
    partial = sum((x ** k) / factorial(k) for k in range(terms + 1))
    nxt = (x ** (terms + 1)) / factorial(terms + 1)
    # For k>=terms+1 the ratio of consecutive terms is <=x/(terms+2).
    upper = partial + nxt / (1 - x / Q(terms + 2))
    return partial, upper


def check_omega_interval() -> None:
    lo = Q(5671432904097838, 10**16)
    hi = Q(5671432904097840, 10**16)
    exp_lo_lower, exp_lo_upper = exp_bounds_positive(lo)
    exp_hi_lower, _ = exp_bounds_positive(hi)
    assert lo * exp_lo_upper < 1
    assert hi * exp_hi_lower > 1
    print("PASS exact certificate: 0.5671432904097838 < W(1) < 0.5671432904097840")


# --- Small multivariate exact checker for Good's formula --------------------

def mv_clean(a: MV) -> MV:
    return {i: c for i, c in a.items() if c}


def mv_add(a: MV, b: MV) -> MV:
    out = dict(a)
    for i, c in b.items():
        out[i] = out.get(i, Q(0)) + c
    return mv_clean(out)


def mv_sub(a: MV, b: MV) -> MV:
    return mv_add(a, {i: -c for i, c in b.items()})


def mv_scale(c: Q, a: MV) -> MV:
    return mv_clean({i: c * x for i, x in a.items()})


def mv_mul(a: MV, b: MV, bounds: MI) -> MV:
    out: MV = {}
    for i, x in a.items():
        for j, y in b.items():
            k = tuple(i[r] + j[r] for r in range(len(bounds)))
            if all(k[r] <= bounds[r] for r in range(len(bounds))):
                out[k] = out.get(k, Q(0)) + x * y
    return mv_clean(out)


def mv_one(d: int) -> MV:
    return {(0,) * d: Q(1)}


def mv_var(d: int, j: int) -> MV:
    i = [0] * d
    i[j] = 1
    return {tuple(i): Q(1)}


def mv_pow(a: MV, k: int, bounds: MI) -> MV:
    out = mv_one(len(bounds))
    base = a
    while k:
        if k & 1:
            out = mv_mul(out, base, bounds)
        base = mv_mul(base, base, bounds)
        k //= 2
    return out


def mv_compose(a: MV, gs: Sequence[MV], bounds: MI) -> MV:
    out: MV = {}
    for idx, coeff in a.items():
        term = mv_one(len(bounds))
        for j, e in enumerate(idx):
            term = mv_mul(term, mv_pow(gs[j], e, bounds), bounds)
        out = mv_add(out, mv_scale(coeff, term))
    return out


def mv_derivative(a: MV, j: int) -> MV:
    out: MV = {}
    for idx, c in a.items():
        if idx[j]:
            k = list(idx)
            k[j] -= 1
            out[tuple(k)] = c * idx[j]
    return mv_clean(out)


def mv_reciprocal(a: MV, bounds: MI) -> MV:
    d = len(bounds)
    zero = (0,) * d
    c = a.get(zero, Q(0))
    assert c != 0
    # a=c(1+r), so a^-1=c^-1 sum_{k=0}^{sum bounds}(-r)^k.
    r = mv_scale(1 / c, mv_sub(a, {zero: c}))
    out = mv_one(d)
    term = mv_one(d)
    for _ in range(1, sum(bounds) + 1):
        term = mv_mul(term, mv_scale(Q(-1), r), bounds)
        out = mv_add(out, term)
    return mv_scale(1 / c, out)


def mv_fixed_point(phis: Sequence[MV], bounds: MI) -> List[MV]:
    d = len(bounds)
    gs = [{} for _ in range(d)]
    xs = [mv_var(d, j) for j in range(d)]
    for _ in range(sum(bounds) + 2):
        gs = [mv_mul(xs[j], mv_compose(phis[j], gs, bounds), bounds) for j in range(d)]
    return gs


def check_multivariate_good() -> None:
    bounds = (3, 3)
    one = mv_one(2)
    x, y = mv_var(2, 0), mv_var(2, 1)
    phi1 = mv_add(mv_add(one, x), y)
    phi2 = mv_add(mv_add(one, x), mv_scale(Q(2), y))
    phis = [phi1, phi2]
    h = mv_add(mv_add(mv_add(one, mv_scale(Q(3), x)), mv_scale(Q(-2), y)), mv_mul(x, y, bounds))
    gs = mv_fixed_point(phis, bounds)
    lhs = mv_compose(h, gs, bounds)

    # D_ij = delta_ij - x_j * (partial_j phi_i) / phi_i.
    invs = [mv_reciprocal(p, bounds) for p in phis]
    dmat: List[List[MV]] = [[{} for _ in range(2)] for _ in range(2)]
    vars_ = [x, y]
    for i in range(2):
        for j in range(2):
            delta = one if i == j else {}
            correction = mv_mul(vars_[j], mv_mul(mv_derivative(phis[i], j), invs[i], bounds), bounds)
            dmat[i][j] = mv_sub(delta, correction)
    det = mv_sub(mv_mul(dmat[0][0], dmat[1][1], bounds), mv_mul(dmat[0][1], dmat[1][0], bounds))

    for n0 in range(0, 4):
        for n1 in range(0, 4):
            rhs = h
            rhs = mv_mul(rhs, mv_pow(phi1, n0, bounds), bounds)
            rhs = mv_mul(rhs, mv_pow(phi2, n1, bounds), bounds)
            rhs = mv_mul(rhs, det, bounds)
            idx = (n0, n1)
            assert lhs.get(idx, Q(0)) == rhs.get(idx, Q(0)), (
                idx, lhs.get(idx, Q(0)), rhs.get(idx, Q(0))
            )
    print("PASS bivariate Good-Lagrange formula on all coefficients in a 4x4 box")


def check_associahedron_normalization_audit() -> None:
    # For f(w)=w+c*w^2/2, the exponential inverse coefficient is g_2=-c.
    c = Q(7, 3)
    f = [Q(0), Q(1), c / 2]
    g = compositional_inverse(f, 2)
    assert factorial(2) * g[2] == -c
    # Correct ordinary coefficient is c_1=c/2; the a_1 face formula gives d_1=-c/2.
    assert g[2] == -c / 2
    print("PASS associahedron normalization audit: corrected formula gives g_2=-f_2")


def main() -> None:
    check_univariate_lagrange()
    check_inverse_and_bell()
    check_algebraic_family()
    check_lambert_w()
    check_shifted_lambert()
    check_catalan()
    check_omega_interval()
    check_multivariate_good()
    check_associahedron_normalization_audit()
    print("ALL EXACT CHECKS PASSED")


if __name__ == "__main__":
    main()
