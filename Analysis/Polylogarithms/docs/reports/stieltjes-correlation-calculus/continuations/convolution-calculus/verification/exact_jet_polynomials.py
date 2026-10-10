#!/usr/bin/env python3
"""Reproduce exact symbolic checks of the negative-integer jet collision terms.

Requirements: Python 3 and SymPy. Run:

    python exact_jet_polynomials.py

The output exact_jet_polynomials.json is written beside this script. No
floating-point arithmetic, numerical differentiation, or numerical fitting is
used. The calculations consist of finite symbolic differentiation, polynomial
truncation, coefficient extraction, and polynomial integration.

The standard special-function identities used in the reductions are

    psi(n+1) = H_n - EulerGamma,
    psi_1(n+1) = zeta(2) - H_n^(2),
    zeta(2) = pi^2/6,  zeta(4) = pi^4/90,
    log Gamma(1-z) = EulerGamma*z + sum_{j>=2} zeta(j)*z^j/j.

Here p is an arbitrary nonnegative integer. The beta germ is normalized by its
nonzero value at the origin before taking logarithmic derivatives, so no
logarithm of the sign (-1)^(p+1) is needed. For the second jet, total degree four
is sufficient: higher-degree terms cannot contribute to [u^2 v^2].
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


def total_degree_truncation(expression, variables, degree):
    """Exact projection of a polynomial onto total degrees at most degree."""
    polynomial = sp.Poly(sp.expand(expression), *variables)
    return sp.Add(
        *(
            coefficient
            * sp.Mul(*(variable**power for variable, power in zip(variables, powers)))
            for powers, coefficient in polynomial.terms()
            if sum(powers) <= degree
        )
    )


def truncated_exponential(logarithm, variables, degree):
    """Exact exponential to a finite degree; logarithm has zero constant term."""
    assert logarithm.subs(dict.fromkeys(variables, 0)) == 0
    term = sp.Integer(1)
    result = term
    for order in range(1, degree + 1):
        term = total_degree_truncation(term * logarithm / order, variables, degree)
        result += term
    return total_degree_truncation(result, variables, degree)


def exact_zero(expression):
    reduced = sp.simplify(expression)
    assert reduced == 0, f"An exact symbolic check failed: {reduced}"
    return str(reduced)


def main():
    p = sp.symbols("p", integer=True, nonnegative=True)
    u, v, a, x, t = sp.symbols("u v a x t")
    ell, T = sp.symbols("ell T")
    Z2, Z3, Z4 = sp.symbols("Z2 Z3 Z4")
    w, difference = u + v, u - v
    at_origin = {u: 0, v: 0}

    # A logarithm of K_p(u,v)/K_p(0,0), holomorphic at (0,0).
    log_normalized_beta_germ = (
        sp.loggamma(p + 1 - u)
        + sp.loggamma(p + 1 - v)
        - sp.loggamma(2 * p + 2 - w)
        - 2 * sp.loggamma(p + 1)
        + sp.loggamma(2 * p + 2)
        + sp.log(sp.cos(sp.pi * difference / 2))
        - sp.log(sp.cos(sp.pi * w / 2))
    )
    raw_first = sp.diff(log_normalized_beta_germ, u).subs(at_origin)
    raw_mixed = sp.diff(log_normalized_beta_germ, u, v).subs(at_origin)
    integer_polygamma_rules = {
        sp.polygamma(0, p + 1): sp.harmonic(p) - sp.EulerGamma,
        sp.polygamma(0, 2 * p + 2): sp.harmonic(2 * p + 1) - sp.EulerGamma,
        sp.polygamma(1, 2 * p + 2): sp.zeta(2) - sp.harmonic(2 * p + 1, 2),
    }
    first = sp.simplify(raw_first.xreplace(integer_polygamma_rules))
    mixed = sp.simplify(raw_mixed.xreplace(integer_polygamma_rules))
    expected_first = sp.harmonic(2 * p + 1) - sp.harmonic(p)
    expected_mixed = sp.harmonic(2 * p + 1, 2) + sp.pi**2 / 3
    first_residual = exact_zero(first - expected_first)
    mixed_residual = exact_zero(mixed - expected_mixed)
    beta_normalization = (
        (-1) ** (p + 1) * sp.factorial(p) ** 2 / (2 * sp.factorial(2 * p + 1))
    )
    normalization_residual = exact_zero(
        (-1) ** (p + 1) * sp.gamma(p + 1) ** 2 / (2 * sp.gamma(2 * p + 2))
        - beta_normalization
    )
    first_jet_polynomial = (ell - expected_first) ** 2 + expected_mixed

    # K_0/K_0(0,0) = Gamma(1-u)Gamma(1-v)/Gamma(1-w)/(1-w)
    #                 * cos(pi*(u-v)/2)/cos(pi*w/2).
    # Including exp(-(u+v)*log(a)) makes the linear coefficient T=1-log(a).
    zetas = {2: Z2, 3: Z3, 4: Z4}
    log_gamma_ratio = sum(
        zetas[j] * (u**j + v**j - w**j) / j for j in range(2, 5)
    )
    minus_log_one_minus_w = sum(w**j / sp.Integer(j) for j in range(1, 5))
    log_cosine_series = sp.series(sp.log(sp.cos(sp.pi * t / 2)), t, 0, 5).removeO()
    log_cosine_series = log_cosine_series.xreplace(
        {sp.pi**2: 6 * Z2, sp.pi**4: 90 * Z4}
    )
    log_cosine_ratio = log_cosine_series.subs(t, difference) - log_cosine_series.subs(t, w)
    full_logarithm = sp.expand(
        (T - 1) * w + log_gamma_ratio + minus_log_one_minus_w + log_cosine_ratio
    )
    formal_exponential = truncated_exponential(full_logarithm, (u, v), 4)
    raw_second_jet = sp.expand(
        sp.factorial(2) ** 2 * formal_exponential.coeff(u, 2).coeff(v, 2)
    )
    expected_raw = (
        T**4 + (6 + 8 * Z2) * T**2 + 8 * (1 - Z3) * T
        + 9 + 8 * Z2 + 8 * Z2**2 - 6 * Z4
    )
    raw_second_residual = exact_zero(raw_second_jet - expected_raw)
    reduced_second_jet = sp.expand(raw_second_jet.subs(Z2**2, sp.Rational(5, 2) * Z4))
    expected_reduced = (
        T**4 + (6 + 8 * Z2) * T**2 + 8 * (1 - Z3) * T
        + 9 + 8 * Z2 + 14 * Z4
    )
    reduced_second_residual = exact_zero(reduced_second_jet - expected_reduced)

    # Independent real-space polynomial integral for zeta(0,x)=1/2-x.
    # For 0<a<1, split where x+a crosses the period boundary.
    bernoulli_correlation = sp.expand(
        sp.integrate((sp.Rational(1, 2) - x) * (sp.Rational(1, 2) - x - a), (x, 0, 1 - a))
        + sp.integrate((sp.Rational(1, 2) - x) * (sp.Rational(3, 2) - x - a), (x, 1 - a, 1))
    )
    bernoulli_expected = sp.bernoulli(2, a) / 2
    bernoulli_residual = exact_zero(bernoulli_correlation - bernoulli_expected)
    bernoulli_collision = beta_normalization.subs(p, 0) * a
    bernoulli_collision_residual = exact_zero(bernoulli_collision + a / 2)
    bernoulli_analytic_part = sp.expand(bernoulli_correlation - bernoulli_collision)
    bernoulli_analytic_residual = exact_zero(
        bernoulli_analytic_part - (sp.Rational(1, 12) + a**2 / 2)
    )

    results = {
        "method": "Exact finite symbolic manipulation; no numerical evaluations.",
        "sympy_version": sp.__version__,
        "symbol_conventions": {
            "p": "An arbitrary nonnegative integer.",
            "ell": "log(a), with 0<a<1.",
            "T": "1-log(a).",
            "Z2": "zeta(2).", "Z3": "zeta(3).", "Z4": "zeta(4).",
            "harmonic(n, j)": "The generalized harmonic number H_n^(j).",
        },
        "first_jet": {
            "log_germ_du_raw": str(raw_first),
            "log_germ_du_reduced": str(first),
            "log_germ_du_residual": first_residual,
            "log_germ_du_dv_raw": str(raw_mixed),
            "log_germ_du_dv_reduced": str(mixed),
            "log_germ_du_dv_residual": mixed_residual,
            "Kp_at_origin": str(beta_normalization),
            "Kp_at_origin_residual": normalization_residual,
            "collision_polynomial_after_dividing_by_Kp_at_origin": str(first_jet_polynomial),
            "collision_term": "Kp_at_origin * a**(2*p+1) * collision_polynomial",
        },
        "second_jet_p0_r2": {
            "total_degree_used": 4,
            "log_cosine_series_through_degree_four": str(log_cosine_series),
            "raw_polynomial": str(raw_second_jet),
            "raw_polynomial_residual": raw_second_residual,
            "reduction": "Z2**2 = 5*Z4/2",
            "reduced_polynomial": str(reduced_second_jet),
            "reduced_polynomial_residual": reduced_second_residual,
            "collision_term": str(-a * expected_reduced / 2),
        },
        "bernoulli_p0_r0": {
            "direct_correlation_integral": str(bernoulli_correlation),
            "bernoulli_polynomial_expression": str(bernoulli_expected),
            "direct_integral_residual": bernoulli_residual,
            "collision_term_from_beta_germ": str(bernoulli_collision),
            "collision_residual": bernoulli_collision_residual,
            "analytic_part": str(bernoulli_analytic_part),
            "analytic_part_residual": bernoulli_analytic_residual,
        },
        "all_exact_checks_passed": True,
    }
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
