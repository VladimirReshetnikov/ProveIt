#!/usr/bin/env python3
"""Exact first-correction coefficients for r=3 and r=5.

Implements Sections 7--8 of article.tex using algebraic root derivatives and
rational Gaussian moments. No recurrence guess, numerical fit, or network is
used. Requires Python >= 3.10 and SymPy.
"""
from __future__ import annotations

from functools import lru_cache
import sympy as sp


def first_correction(r: int) -> sp.Expr:
    """Return the exact coefficient d_1(r) for one of the supported rows."""
    if r not in (3, 5):
        raise ValueError("This exact implementation supports r=3 or r=5")

    steps = list(range(-(r // 2), r // 2 + 1))
    dimension = r - 2
    C = sp.zeros(dimension, r)
    for j in range(dimension):
        C[j, j] = 1
        C[j, j + 1] = -2
        C[j, j + 2] = 1
    Q = C * C.T / r
    covariance = Q.inv()
    sigma2 = sum(sp.Rational(s * s, r) for s in steps)
    coordinates = sp.symbols(f"z:{dimension}")
    u = sp.Symbol("u")
    linear_forms = [
        sum(C[j, i] * coordinates[j] for j in range(dimension))
        for i in range(r)
    ]
    P = sum(u**s for s in steps) / r
    a = -steps[0]
    deflated = sp.cancel(
        (sum(u ** (a + s) for s in steps) - r * u**a) / (u - 1)**2
    )
    # Select the required branch by an exact radical and exact inequalities.
    small_roots = [] if r == 3 else [(-3 + sp.sqrt(5)) / 2]
    for root in small_roots:
        assert sp.simplify(deflated.subs(u, root)) == 0
        assert -1 < root < 0

    # Principal small root: u(t) = 1 + v1*s + v2*s^2 + v3*s^3 + ...,
    # with t = 1-s^2. Equations (8.3)--(8.4) of the article.
    P2, P3, P4 = (sp.diff(P, u, j).subs(u, 1) for j in (2, 3, 4))
    v1 = -sp.sqrt(2 / P2)
    v2 = -P3 * v1**2 / (6 * P2)
    v3 = sp.simplify(
        (1 - P2*v2**2/2 - P3*v1**2*v2/2 - P4*v1**4/24) / (P2*v1)
    )
    g1_ratio = sp.simplify(
        sp.Rational(3, 8) - sp.Rational(3, 2) * (
            v3/v1 + 1
            + sum(1/(root*sp.diff(P, u).subs(u, root)) for root in small_roots)
        )
    )

    # Gradient and Hessian of log(E_*) at zero markings.
    logE_gradient = -C[:, 0]
    logE_hessian = Q - sp.Matrix(
        dimension, dimension,
        lambda j, k: sum(
            sp.Rational(steps[i], r)*C[j, i]*C[k, i] for i in range(r)
        ) / sigma2,
    )
    for root in small_roots:
        Pu = sp.simplify(sp.diff(P, u).subs(u, root))
        Puu = sp.simplify(sp.diff(P, u, 2).subs(u, root))
        Pz = sp.Matrix([
            sum(C[j, i]*root**steps[i] for i in range(r))/r
            for j in range(dimension)
        ])
        Puz = sp.Matrix([
            sum(C[j, i]*steps[i]*root**(steps[i]-1) for i in range(r))/r
            for j in range(dimension)
        ])
        root_gradient = sp.simplify(-Pz/Pu)
        logE_gradient += root_gradient/root
        for j in range(dimension):
            for k in range(dimension):
                Pzz = sum(
                    C[j, i]*C[k, i]*root**steps[i] for i in range(r)
                ) / r
                logE_hessian[j, k] += (
                    Q[j, k] - Pzz
                    - Puz[j]*root_gradient[k] - Puz[k]*root_gradient[j]
                    - Puu*root_gradient[j]*root_gradient[k]
                ) / (root*Pu) - root_gradient[j]*root_gradient[k]/root**2
    logE_gradient = sp.simplify(logE_gradient)
    logE_hessian = sp.simplify(logE_hessian)

    # Variance derivatives, then derivatives of a(z)=G0(z)/G0(0).
    variance_gradient = sp.Matrix([
        sum(sp.Rational(steps[i]**2, r)*C[j, i] for i in range(r))
        for j in range(dimension)
    ])
    variance_hessian = sp.Matrix(
        dimension, dimension,
        lambda j, k: sum(
            sp.Rational(steps[i]**2, r)*C[j, i]*C[k, i] for i in range(r)
        ) - sigma2*Q[j, k],
    )
    amplitude_gradient = sp.simplify(logE_gradient - variance_gradient/(2*sigma2))
    amplitude_hessian = sp.simplify(
        logE_hessian - variance_hessian/(2*sigma2)
        + variance_gradient*variance_gradient.T/(2*sigma2**2)
        + amplitude_gradient*amplitude_gradient.T
    )
    M2 = sum(v**2 for v in linear_forms)/r
    M3 = sum(v**3 for v in linear_forms)/r
    M4 = sum(v**4 for v in linear_forms)/r
    M12 = sum(steps[i]*linear_forms[i]**2 for i in range(r))/r
    lambda4 = (M4 - 3*M2**2)/24 - M12**2/(8*sigma2)

    @lru_cache(None)
    def gaussian_moment(powers: tuple[int, ...]) -> sp.Expr:
        """Wick recursion for a centered Gaussian with covariance Q^{-1}."""
        degree = sum(powers)
        if degree == 0:
            return sp.Integer(1)
        if degree % 2:
            return sp.Integer(0)
        j = next(i for i, value in enumerate(powers) if value)
        remaining = list(powers)
        remaining[j] -= 1
        total = sp.Integer(0)
        for k, multiplicity in enumerate(remaining):
            if multiplicity:
                reduced = remaining.copy()
                reduced[k] -= 1
                total += (
                    multiplicity*covariance[j, k]*gaussian_moment(tuple(reduced))
                )
        return total

    def gaussian_mean(polynomial: sp.Expr) -> sp.Expr:
        return sp.simplify(sum(
            coefficient*gaussian_moment(powers)
            for powers, coefficient in sp.Poly(
                sp.expand(polynomial), coordinates
            ).terms()
        ))

    correction = sp.simplify((
        g1_ratio - sp.trace(covariance*amplitude_hessian)/2
        + gaussian_mean(
            sum(amplitude_gradient[j]*coordinates[j] for j in range(dimension))
            * M3/6 + lambda4 - M3**2/72
        )
    ) / r)
    print(f"r={r}: G1/G0={g1_ratio}; d1={correction}; decimal={sp.N(correction, 20)}")
    multinomial_correction = sp.simplify(
        correction - (sp.Rational(1, r)-r)/12
    )
    print(f"  Multinomial-normalized correction: {multinomial_correction}")
    return correction


if __name__ == "__main__":
    results = {r: first_correction(r) for r in (3, 5)}
    assert results[3] == -sp.Rational(11, 9)
    assert sp.simplify(results[5] + sp.Rational(13, 10) - 13*sp.sqrt(5)/50) == 0
    print("PASS: exact first-correction coefficients")
