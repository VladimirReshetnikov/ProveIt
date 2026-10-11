#!/usr/bin/env python3
"""Exact symbolic certificates for the shifted height-one Laurent formulas.

No numerical fitting is used.  The output records b_k, finite parts, principal
parts, and exact differential and Bernoulli cross-checks.  Run with Python 3
and SymPy.  This is an algebraic check accompanying the analytic proof, not a
substitute for the Mellin continuation and interchange arguments.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


def main() -> None:
    a, u, t, gamma = sp.symbols("a u t gamma")
    max_m, max_r = 4, 5
    zeta = {k: sp.Symbol(f"zeta_{k}") for k in range(2, max_r + 3)}

    # Coefficients of log(phi), obtained from the even Bernoulli expansion.
    log_phi = {1: (u - 2*a - 1)/2}
    for k in range(2, max_m + 4):
        log_phi[k] = (-(1+u)*sp.bernoulli(k)/(k*sp.factorial(k))
                      if k % 2 == 0 else sp.S.Zero)
    b = [sp.S.One]
    for n in range(1, max_m + 3):
        b.append(sp.expand(sum(k*log_phi[k]*b[n-k]
                               for k in range(1, n+1))/n))

    # Independent finite Taylor expansion of the defining analytic expression.
    t_over = sp.series(t/(1-sp.exp(-t)), t, 0, 5).removeO()
    direct_log = sp.series(sp.log(t_over), t, 0, 5).removeO()
    direct_phi = sp.series(sp.exp(-(a+1)*t+(1+u)*direct_log),
                           t, 0, 5).removeO().expand()
    b_checks = [sp.expand(b[k]-direct_phi.coeff(t, k)) == 0
                for k in range(5)]
    assert all(b_checks)

    # C(u)=1/Gamma(1+u), calculated as a formal exponential recurrence.
    c = [sp.S.One]
    for n in range(1, max_r + 2):
        value = gamma*c[n-1]
        value += sum((-1)**(k+1)*zeta[k]*c[n-k]
                     for k in range(2, n+1))
        c.append(sp.expand(value/n))
    C = sum(c[k]*u**k for k in range(len(c)))

    # Reciprocal Gamma at each negative integer via the exact Gamma recurrence.
    reciprocal = []
    for m in range(max_m + 2):
        P = u*C
        for j in range(1, m+1):
            P *= u-j
        reciprocal.append(sp.Poly(sp.expand(P), u))

    A = []
    for m in range(max_m + 2):
        product = sp.Poly(sp.expand(b[m+1]*reciprocal[m].as_expr()), u)
        A.append([sp.expand(product.coeff_monomial(u**d))
                  for d in range(max_r+2)])

    # Leading coefficient must give the ordinary Hurwitz value at -m.
    bernoulli_checks = [sp.expand(A[m][1]
                        +sp.bernoulli(m+1, a+1)/(m+1)) == 0
                        for m in range(max_m+1)]
    assert all(bernoulli_checks)

    # The residue correction is a structurally independent differential check.
    derivative_checks = []
    for m in range(max_m+1):
        for r in range(max_r+1):
            rhs = -c[r] if m == 0 else m*A[m-1][r+1]-A[m-1][r]
            ok = sp.expand(sp.diff(A[m][r+1], a)-rhs) == 0
            derivative_checks.append({"m": m, "r": r, "passed": ok})
    assert all(item["passed"] for item in derivative_checks)

    # Uniform reflection and polynomial antiderivative rules, checked in all
    # displayed depths.  The extra m=5 array above is needed only to check
    # the antiderivative at m=4.
    reflection_checks, primitive_checks = [], []
    for m in range(max_m+1):
        for r in range(max_r+1):
            reflected = (-1)**(m+1)*sum(
                sp.diff(A[m][r-j+1], a, j)/sp.factorial(j)
                for j in range(r+1))
            reflection_ok = sp.expand(
                A[m][r+1].subs(a, -1-a)-reflected) == 0
            reflection_checks.append({"m": m, "r": r,
                                      "passed": reflection_ok})
            primitive = sum(A[m+1][r-j+1]/sp.Integer(m+1)**(j+1)
                            for j in range(r+1))
            primitive_ok = sp.expand(sp.diff(primitive, a)-A[m][r+1]) == 0
            primitive_checks.append({"m": m, "r": r,
                                     "passed": primitive_ok})
    assert all(item["passed"] for item in reflection_checks)
    assert all(item["passed"] for item in primitive_checks)

    # Multiplication: derive L_q(t) directly as the logarithm of a finite
    # geometric sum, independently of the generalized-Bernoulli compiler.
    # Gamma recurrence factors are retained explicitly, including A_{-1}=C.
    multiplication_checks, multiplication_d = [], {}
    A_polynomial = {m: sum(A[m][d]*u**d for d in range(max_r+2))
                    for m in range(max_m+1)}
    A_polynomial[-1] = C
    for q in (2, 3):
        Lq = sp.series(sp.log(sum(sp.exp(-sp.Rational(j,q)*t)
                                for j in range(q))/q),
                       t, 0, max_m+2).removeO().expand()
        d = [sp.S.One]
        for n in range(1,max_m+2):
            d.append(sp.expand(-u*sum(k*Lq.coeff(t,k)*d[n-k]
                                     for k in range(1,n+1))/n))
        multiplication_d[str(q)] = [str(sp.factor(x)) for x in d]
        for m in range(max_m+1):
            rhs = sp.Poly(sp.expand(sum(
                sp.Integer(q)**(n-m)*d[n]*sp.rf(u-m,n)*A_polynomial[m-n]
                for n in range(m+2))), u)
            for r in range(max_r+1):
                lhs = sum(A[m][r+1].subs(a,(a+1+j)/q-1)
                          for j in range(q))
                difference = sp.expand(lhs-rhs.coeff_monomial(u**(r+1)))
                ok = difference == 0
                multiplication_checks.append({"q": q, "m": m, "r": r,
                                               "passed": ok})
    assert all(item["passed"] for item in multiplication_checks)

    # Four additional half-shift displays, with every nonpositive Laurent
    # power included so that an accidentally omitted pole would be detected.
    epsilon = sp.Symbol("epsilon")
    half_expected = {
        (1,1): 1/(24*epsilon)+gamma/24,
        (2,1): 1/(24*epsilon**2)+gamma/(24*epsilon)
                  +(gamma**2-zeta[2]-8)/48,
        (1,2): -sp.Rational(1,24),
        (2,2): -1/(24*epsilon)+(1-2*gamma)/48,
    }
    half_checks = []
    for (r,m), expected_value in half_expected.items():
        actual = sum(A[m][r+1-h].subs(a,-sp.Rational(1,2))*epsilon**(-h)
                     for h in range(r+1))
        ok = sp.expand(actual-expected_value) == 0
        half_checks.append({"m": m, "r": r, "passed": ok,
                            "principal_and_finite": str(sp.expand(actual))})
    assert all(item["passed"] for item in half_checks)

    # Check all displayed odd-denominator identities by harmonic recurrences.
    H = {k: sp.Symbol(f"H_{k}") for k in range(1, 5)}
    h = [sp.S.One]
    for d in range(1, 5):
        h.append(sp.expand(sum(H[k]*h[d-k] for k in range(1,d+1))/d))
    L = sp.Symbol("L")
    ordinary_zeta = lambda k: sp.zeta(k)  # Evaluates even values exactly.
    subs = {H[1]: -2*L}
    subs.update({H[k]: (2-2**k)*ordinary_zeta(k) for k in range(2,5)})
    odd_values = {}
    for r in range(1,4):
        value = sum((2**(k+1)-1)*ordinary_zeta(k+1)*h[r+1-k]
                    for k in range(1,r+2))
        odd_values[r] = sp.expand(sp.factorial(r)*value.subs(subs)/4)
    expected = {
        1: (7*sp.zeta(3)-sp.pi**2*L)/4,
        2: sp.pi**2*L**2/2-7*L*sp.zeta(3)+sp.pi**4/24,
        3: sp.Rational(3,2)*(31*sp.zeta(5)-13*sp.zeta(2)*sp.zeta(3)
            -15*L*sp.zeta(4)+14*L**2*sp.zeta(3)-4*L**3*sp.zeta(2)),
    }
    odd_checks = {r: sp.simplify(odd_values[r]-expected[r]) == 0
                  for r in odd_values}
    assert all(odd_checks.values())

    records = []
    for m in range(max_m+1):
        for r in range(max_r+1):
            records.append({
                "m": m,
                "r": r,
                "point": -m,
                "finite_part": str(sp.factor(A[m][r+1])),
                "finite_part_a0": str(sp.factor(A[m][r+1].subs(a, 0))),
                "principal_coefficients": {
                    str(-order): str(sp.factor(A[m][r+1-order]))
                    for order in range(1,r+1)
                },
            })

    report = {
        "description": "Exact polynomial checks of the harmonic Laurent section",
        "sympy_version": sp.__version__,
        "b_polynomials": {str(k): str(sp.factor(b[k])) for k in range(len(b))},
        "reciprocal_gamma_at_one_coefficients": [str(x) for x in c],
        "direct_defining_series_checks": b_checks,
        "ordinary_hurwitz_bernoulli_checks": bernoulli_checks,
        "finite_part_derivative_checks": derivative_checks,
        "finite_part_reflection_checks": reflection_checks,
        "finite_part_primitive_checks": primitive_checks,
        "finite_part_multiplication_checks": multiplication_checks,
        "multiplication_kernel_coefficients": multiplication_d,
        "half_shift_laurent_display_checks": half_checks,
        "odd_denominator_display_checks": odd_checks,
        "odd_denominator_values": {str(r): str(odd_values[r]) for r in odd_values},
        "laurent_records": records,
        "all_checks_passed": True,
    }
    path = Path(__file__).with_name("harmonic_coefficients.json")
    path.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"all_checks_passed": True,
                      "direct_series_checks": len(b_checks),
                      "bernoulli_checks": len(bernoulli_checks),
                      "derivative_checks": len(derivative_checks),
                      "reflection_checks": len(reflection_checks),
                      "primitive_checks": len(primitive_checks),
                      "multiplication_checks": len(multiplication_checks),
                      "half_shift_checks": len(half_checks),
                      "odd_denominator_checks": len(odd_checks),
                      "output": str(path)}, indent=2))


if __name__ == "__main__":
    main()
