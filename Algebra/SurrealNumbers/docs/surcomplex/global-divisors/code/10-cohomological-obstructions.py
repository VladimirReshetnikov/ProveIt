#!/usr/bin/env python3
"""Exact finite checks for the accompanying surcomplex-analysis manuscript.

Requirements: Python 3.10+ and SymPy. Run: python verify_examples.py
These are illustrative algebra checks, NOT verification of the general theorems.
No network access or floating-point arithmetic is used.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import Sequence

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required: install sympy in your Python environment.") from exc

z, u, t, s = sp.symbols("z u t s")
REPORT: list[str] = []


def checked(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)
    REPORT.append("PASS  " + description)


def zero(expr: sp.Expr) -> bool:
    return sp.cancel(sp.expand(expr)) == 0


def trunc(expr: sp.Expr, order: int) -> sp.Expr:
    """Retain Laurent powers of t up through order, for our rational inputs."""
    return sp.expand(sp.series(expr, t, 0, order + 1).removeO())


def jet(expr: sp.Expr, degree: int) -> sp.Expr:
    poly = sp.Poly(sp.expand(expr), u)
    return sp.Add(*(poly.nth(j) * u**j for j in range(degree)))


@dataclass(frozen=True)
class Cluster:
    center: int
    multiplicity: int
    polynomial: sp.Expr  # Monic polynomial in the local coordinate u.


def hermite_section(clusters: Sequence[Cluster]):
    """The finite polynomial right inverse of ordinary Hermite evaluation."""
    size = sum(c.multiplicity for c in clusters)
    rows = [
        [sp.binomial(k, j) * sp.Integer(c.center) ** (k-j) if k >= j else 0
         for k in range(size)]
        for c in clusters for j in range(c.multiplicity)
    ]
    inv = sp.Matrix(rows).inv()

    def lift(targets: Sequence[sp.Expr]) -> sp.Expr:
        if len(targets) != len(clusters):
            raise ValueError("One target is required per cluster.")
        values = sp.Matrix([
            sp.Poly(sp.expand(target), u).nth(j)
            for c, target in zip(clusters, targets)
            for j in range(c.multiplicity)
        ])
        coefficients = inv * values
        return sp.expand(sum(coefficients[k] * z**k for k in range(size)))

    return lift


def check_global_divisor_recursion() -> None:
    clusters = [
        Cluster(-1, 2, u**2 + t*u + t**2),
        Cluster(2, 3, u**3 - t + t**2*u),
        Cluster(4, 1, u - 2*t - t**3),
    ]
    order = 7
    lift = hermite_section(clusters)
    f0 = sp.prod((z-c.center)**c.multiplicity for c in clusters)
    f = [sp.expand(f0)]
    q = [[sp.div(sp.expand(f0.subs(z, c.center+u)), u**c.multiplicity, u)[0]]
         for c in clusters]
    for nu in range(1, order+1):
        known = []
        for i, c in enumerate(clusters):
            perturbation = sp.Poly(c.polynomial-u**c.multiplicity, t)
            h = sum(perturbation.nth(alpha) * q[i][nu-alpha]
                    for alpha in range(1, nu+1))
            known.append(sp.expand(h))
        fnu = lift([jet(h, c.multiplicity) for h, c in zip(known, clusters)])
        f.append(fnu)
        for i, c in enumerate(clusters):
            numerator = sp.expand(fnu.subs(z, c.center+u)-known[i])
            quotient, remainder = sp.div(numerator, u**c.multiplicity, u)
            if not zero(remainder):
                raise AssertionError(f"Jet cancellation failed at center {c.center}, order {nu}.")
            q[i].append(quotient)
    result = sp.expand(sum(f[k] * t**k for k in range(order+1)))
    expected = sp.expand(sp.prod(c.polynomial.subs(u, z-c.center) for c in clusters))
    checked(zero(result-expected),
            "Global divisor recursion through t^7 equals the exact product of three perturbed clusters.")
    for i, c in enumerate(clusters):
        local_q = sum(q[i][k]*t**k for k in range(order+1))
        error = result.subs(z, c.center+u)-c.polynomial*local_q
        checked(zero(trunc(error, order)),
                f"Local factorization at center {c.center}, multiplicity {c.multiplicity}, through t^7.")


def check_local_preparation() -> None:
    order = 5
    error = {1: 1+u+u**3, 2: u}
    a = [sp.Integer(0)]
    b = [sp.Integer(0)]
    for nu in range(1, order+1):
        h = sp.expand(error.get(nu, 0)-sum(a[k]*b[nu-k] for k in range(1, nu)))
        an = jet(h, 2)
        bn, remainder = sp.div(sp.expand(h-an), u**2, u)
        if not zero(remainder):
            raise AssertionError("Local preparation Taylor division failed.")
        a.append(an)
        b.append(bn)
    p = u**2+sum(a[k]*t**k for k in range(1, order+1))
    q = 1+sum(b[k]*t**k for k in range(1, order+1))
    h = u**2+t*(1+u+u**3)+t**2*u
    checked(zero(trunc(h-p*q, order)), "Local preparation identity through t^5.")
    REPORT.append("      Prepared polynomial modulo t^6: " + str(sp.expand(p)))


def check_deformed_interpolation() -> None:
    clusters = [Cluster(1, 2, u**2-t-t**2*u), Cluster(3, 1, u+2*t)]
    targets = [t**-1 + u + 2*t**2, -3+t**2]
    order = 4
    lift = hermite_section(clusters)

    def correction(data: Sequence[sp.Expr]) -> list[sp.Expr]:
        f = lift(data)
        output = []
        for c in clusters:
            local = sp.expand(f.subs(z, c.center+u))
            remainder = sp.rem(local, c.polynomial, u, domain=sp.QQ.frac_field(t))
            output.append(trunc(remainder-jet(local, c.multiplicity), order))
        return output

    term = list(targets)
    accumulated = list(targets)
    for _ in range(order+2):
        term = [-value for value in correction(term)]
        accumulated = [trunc(a+b, order) for a, b in zip(accumulated, term)]
    f = lift(accumulated)
    checked(all(zero(value) for value in term),
            "Interpolation Neumann correction terminates at the tested Laurent truncation [-1,4].")
    for c, target in zip(clusters, targets):
        remainder = sp.rem(f.subs(z, c.center+u), c.polynomial, u, domain=sp.QQ.frac_field(t))
        checked(zero(trunc(remainder-target, order)),
                f"Deformed interpolation remainder at center {c.center}, through t^4 (including t^-1 input).")
    # An independently computed finite CRT solution over the rational-function field.
    polys = [c.polynomial.subs(u, z-c.center) for c in clusters]
    product = sp.prod(polys)
    exact = sp.Integer(0)
    for c, p, target in zip(clusters, polys, targets):
        other = sp.div(product, p, z, domain=sp.QQ.frac_field(t))[0]
        inverse = sp.invert(other, p, z, domain=sp.QQ.frac_field(t))
        exact += target.subs(u, z-c.center)*other*inverse
    exact = sp.rem(exact, product, z, domain=sp.QQ.frac_field(t))
    differences = sp.Poly(sp.expand(f-exact), z).all_coeffs()
    checked(all(zero(trunc(coef, order)) for coef in differences),
            "Neumann interpolator agrees with independent finite CRT over Q(t), through t^4.")


def check_selectors_and_residues() -> None:
    for n in range(1, 9):
        p = u**n-s**n
        selector = sum((u/s)**j for j in range(n))/n
        checked(zero(selector.subs(u, s)-1) and
                zero((u-s)*selector-p/(n*s**(n-1))),
                f"Root selector formula for cluster degree {n}.")
        idem = sp.rem(selector**2-selector, p, u, domain=sp.QQ.frac_field(s))
        checked(zero(idem), f"Selector idempotence modulo u^{n}-s^{n}.")
        reciprocal_derivative = u/(n*s**n)
        inverse_error = sp.rem(sp.diff(p, u)*reciprocal_derivative-1, p, u,
                               domain=sp.QQ.frac_field(s))
        root_sum = -sp.Poly(p, u).nth(n-1)
        residue_sum = sp.cancel(root_sum/(n*s**n))
        checked(zero(inverse_error) and residue_sum == (1 if n == 1 else 0),
                f"Residue formula and within-cluster residue sum for degree {n}.")


def check_transition_identities() -> None:
    x, y, r = sp.symbols("x y r")
    order = 8
    log_series = -sum(x**k/k for k in range(1, order+1))
    inverse = sp.series(sp.exp(log_series), x, 0, order+1).removeO()
    checked(zero(inverse-(1-x)), "exp(log(1-x)) = 1-x through x^8.")
    ea = sp.series(sp.exp(r*x), r, 0, 7).removeO()
    eb = sp.series(sp.exp(r*y), r, 0, 7).removeO()
    esum = sp.series(sp.exp(r*(x+y)), r, 0, 7).removeO()
    difference = sp.series(ea*eb-esum, r, 0, 7).removeO()
    checked(zero(difference), "Multiplicative transition law exp(a)exp(b)=exp(a+b) through total degree 6.")
    amplitudes = [2, -3, 5]
    exponents = [3, 2, 1]
    b = [sp.Integer(a)*t**g/(z-n)
         for n, (a, g) in enumerate(zip(amplitudes, exponents), 1)]
    a0 = -sum(b)
    for n, bn in enumerate(b, 1):
        an = sp.cancel(bn+a0)
        checked(zero(an-a0-bn) and sp.residue(an, z, n) == 0,
                f"Finite Cousin splitting and cancellation at center {n}.")


def main() -> int:
    REPORT.extend([
        "EXACT SYMBOLIC CHECKS: HAHN-COHERENT SURCOMPLEX ANALYSIS",
        f"Python {sys.version.split()[0]}; SymPy {sp.__version__}",
        "All computations use exact symbolic arithmetic.",
        "",
    ])
    check_global_divisor_recursion()
    check_local_preparation()
    check_deformed_interpolation()
    check_selectors_and_residues()
    check_transition_identities()
    count = sum(line.startswith("PASS") for line in REPORT)
    REPORT.extend(["", f"RESULT: {count} checks passed.",
                   "These checks do not certify transfinite summability, arbitrary supports,",
                   "sheaf cohomology, novelty, or the general theorems. Those require the proofs."])
    print("\n".join(REPORT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
