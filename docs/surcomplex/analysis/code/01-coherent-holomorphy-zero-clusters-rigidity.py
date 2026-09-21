#!/usr/bin/env python3
"""Exact finite checks for examples in surcomplex_analysis.tex.

Python 3.9+, standard library only. These checks test rational coefficient
identities, not the general theorems or the proper-class foundations.
"""

from fractions import Fraction as Q
from math import factorial
from typing import Dict, List, Tuple

Poly = List[Q]
Laurent = Dict[Tuple[int, int], Q]  # exponent of r, exponent of E = exp(r)


def multiply(a: Poly, b: Poly, degree: int) -> Poly:
    """Multiply polynomials, retaining coefficients through the given degree."""
    out = [Q(0) for _ in range(degree + 1)]
    for i, ai in enumerate(a):
        if not ai or i > degree:
            continue
        for j, bj in enumerate(b[: degree - i + 1]):
            if bj:
                out[i + j] += ai * bj
    return out


def exp_series(a: Poly, degree: int) -> Poly:
    """exp(a) modulo X**(degree+1), for a[0] = 0, via b' = a'b."""
    if not a or a[0] != 0:
        raise ValueError("The input must have zero constant term.")
    out = [Q(1)] + [Q(0) for _ in range(degree)]
    for n in range(1, degree + 1):
        out[n] = sum(
            (k * a[k] * out[n - k] for k in range(1, min(n, len(a) - 1) + 1)),
            Q(0),
        ) / n
    return out


def check_tree_series(degree: int = 40) -> None:
    z = [Q(0)] + [Q(n ** (n - 1), factorial(n)) for n in range(1, degree + 1)]
    ez = exp_series(z, degree - 1)
    for n in range(1, degree + 1):
        assert z[n] == ez[n - 1], f"Tree-series mismatch at degree {n}."
    print(f"PASS: z = eta*exp(z), exact coefficients through eta^{degree}.")
    print("      First six coefficients: " + ", ".join(map(str, z[1:7])))


def check_preparation(t_degree: int = 7, w_degree: int = 10) -> None:
    """Check the graded preparation of w**2 - t*exp(w).

    R_2 lowers w-degree by two per recursion level. Extra working
    precision prevents the discarded high-w-degree tail from polluting
    any coefficient being tested.
    """
    working = w_degree + 2 * t_degree + 6
    p: Dict[int, Poly] = {}
    q: Dict[int, Poly] = {}
    h = [-Q(1, factorial(k)) for k in range(working + 1)]
    for n in range(1, t_degree + 1):
        forcing = h[:] if n == 1 else [Q(0) for _ in range(working + 1)]
        for j in range(1, n):
            product = multiply(p[j], q[n - j], working)
            forcing = [a - b for a, b in zip(forcing, product)]
        p[n] = forcing[:2]
        q[n] = forcing[2:] + [Q(0), Q(0)]

    assert p[1] == [Q(-1), Q(-1)], "First preparation polynomial is incorrect."
    assert p[2] == [Q(-1, 2), Q(-2, 3)], "Second preparation polynomial is incorrect."
    tested = 0
    for n in range(1, t_degree + 1):
        product = [Q(0) for _ in range(working + 1)]
        for k in range(2):
            product[k] += p[n][k]
        for k in range(2, working + 1):
            product[k] += q[n][k - 2]
        for j in range(1, n):
            term = multiply(p[j], q[n - j], working)
            product = [a + b for a, b in zip(product, term)]
        for k in range(w_degree + 1):
            expected = h[k] if n == 1 else Q(0)
            assert product[k] == expected, f"Preparation mismatch at t^{n} w^{k}."
            tested += 1
    print(
        f"PASS: P*(1+Q) = w^2 - t*exp(w), {tested} exact coefficients "
        f"(t^1..t^{t_degree}, w^0..w^{w_degree})."
    )
    print("      p_1 = -t*(1+w); p_2 = -t^2*(1/2 + 2*w/3).")


def l_add(*terms: Laurent) -> Laurent:
    out: Laurent = {}
    for term in terms:
        for power, coefficient in term.items():
            out[power] = out.get(power, Q(0)) + coefficient
    return {power: coefficient for power, coefficient in out.items() if coefficient}


def l_mul(a: Laurent, b: Laurent) -> Laurent:
    out: Laurent = {}
    for (ra, ea), ca in a.items():
        for (rb, eb), cb in b.items():
            power = (ra + rb, ea + eb)
            out[power] = out.get(power, Q(0)) + ca * cb
    return {power: coefficient for power, coefficient in out.items() if coefficient}


def l_scale(a: Laurent, c: Q) -> Laurent:
    return {power: coefficient * c for power, coefficient in a.items() if coefficient * c}


def check_two_scale_root() -> None:
    # z = r + s*a + s^2*b; E is an indeterminate representing exp(r).
    r: Laurent = {(1, 0): Q(1)}
    e: Laurent = {(0, 1): Q(1)}
    a: Laurent = {(-1, 1): Q(1, 2)}
    b: Laurent = {(-2, 2): Q(1, 4), (-3, 2): Q(-1, 8)}
    residual_1 = l_add(l_scale(l_mul(r, a), Q(2)), l_scale(e, Q(-1)))
    residual_2 = l_add(
        l_mul(a, a),
        l_scale(l_mul(r, b), Q(2)),
        l_scale(l_mul(e, a), Q(-1)),
    )
    assert not residual_1, f"Linear residual is nonzero: {residual_1}"
    assert not residual_2, f"Quadratic residual is nonzero: {residual_2}"
    print("PASS: z^2 - r^2 - s*exp(z) = 0 modulo s^3 in Q[r,r^-1,E][[s]].")
    print("      z = r + s*E/(2*r) + s^2*E^2*(2*r-1)/(8*r^3) modulo s^3.")


def main() -> None:
    print("SURCOMPLEX ANALYSIS: EXACT FINITE VERIFICATION")
    print("Arithmetic: Python fractions.Fraction; no floating-point tests.\n")
    check_tree_series()
    check_preparation()
    check_two_scale_root()
    print("\nAll checks passed.")
    print("Scope: finite algebraic checks of examples, not formal verification of the theorems.")


if __name__ == "__main__":
    main()
