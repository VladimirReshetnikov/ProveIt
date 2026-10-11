#!/usr/bin/env python3
"""Exact finite checks for the scalar and differential Gamma normalizers.

Requires Python 3.10+ and SymPy.  No floating-point evaluation, numerical
sampling, or fitted coefficients are used.  Harmonic sums, Euler's
constant, odd zeta values, polygamma derivatives, and the strict-depth
Laurent constants are independent formal symbols.  Even zeta values are
reduced only by their exact Bernoulli-number formula when required.

Run:
    python verify_scalar.py
    python verify_scalar.py --output ../results/scalar_verification.json

The default report is scalar_verification.json beside this script.
These finite symbolic checks supplement the analytic proofs in the
article; they do not establish convergence or an all-degree theorem.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import platform

import sympy as sp


DIFFERENTIAL_DEGREE = 5
CONVOLUTION_DEGREE = 10


def exponential_coefficients(log_coefficients, degree):
    """Coefficients of exp(sum a_r t^r), by finite product multiplication.

    This uses the truncated product of exp(a_r t^r).  It does not use
    any of the Bell, Appell, or reciprocal-Gamma recurrences checked
    below, so those recurrences are tested by an independent assembly.
    """
    result = [sp.S.One] + [sp.S.Zero] * degree
    for r in range(1, degree + 1):
        a = sp.sympify(log_coefficients.get(r, 0))
        if a == 0:
            continue
        factor = {r * j: a**j / sp.factorial(j)
                  for j in range(degree // r + 1)}
        result = [sp.expand(sum(result[n - k] * value
                                for k, value in factor.items() if k <= n))
                  for n in range(degree + 1)]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().with_name("scalar_verification.json"),
        help="JSON report path (default: beside this script)")
    args = parser.parse_args()

    M, N = DIFFERENTIAL_DEGREE, CONVOLUTION_DEGREE
    Y, gamma, v = sp.symbols("Y gamma v")
    zeta = {r: sp.Symbol(f"zeta{r}") for r in range(2, N + 1)}
    H = {r: sp.Symbol(f"H{r}") for r in range(1, M + 1)}
    psi = sp.symbols(f"psi0:{M + 1}")
    lam = {d: sp.Symbol(f"lambda{d}") for d in range(1, N)}
    even_zeta = {
        zeta[2 * k]: (-1)**(k + 1) * sp.bernoulli(2 * k)
        * (2 * sp.pi)**(2 * k) / (2 * sp.factorial(2 * k))
        for k in range(1, N // 2 + 1)
    }
    checks = []

    def check(name, lhs, rhs=0, *, reduce_even=False, degree=None):
        residual = sp.expand(lhs - rhs)
        if reduce_even:
            residual = sp.expand(residual.xreplace(even_zeta))
        if residual != 0:
            raise AssertionError(f"{name}: nonzero exact residual {residual}")
        item = {"name": name, "residual": "0"}
        if degree is not None:
            item["degree"] = degree
        if reduce_even:
            item["even_zeta_reduction"] = True
        checks.append(item)

    # The formal Gamma-Appell generator, assembled by the finite product.
    p_log = {1: Y + gamma}
    p_log.update({r: zeta[r] / r for r in range(2, M + 1)})
    p_coeff = exponential_coefficients(p_log, M)
    P = [sp.expand(sp.factorial(m) * p_coeff[m]) for m in range(M + 1)]
    hcenter = Y + gamma
    displayed_P = {
        0: sp.S.One,
        1: hcenter,
        2: hcenter**2 + zeta[2],
        3: hcenter**3 + 3 * zeta[2] * hcenter + 2 * zeta[3],
    }
    for m, expected in displayed_P.items():
        check("displayed_scalar_polynomial", P[m], expected, degree=m)
    for m in range(1, M + 1):
        check("Appell_derivative", sp.diff(P[m], Y), m * P[m - 1], degree=m)
    for m in range(M):
        recurrence = ((Y + gamma) * P[m]
                      + sum(sp.binomial(m, r) * sp.factorial(r) * zeta[r + 1]
                            * P[m - r] for r in range(1, m + 1)))
        check("scalar_finite_recurrence", P[m + 1], recurrence, degree=m + 1)

    # Independent finite-order control of the universal cotangent residue.
    cotangent = -1 / v + sum(2 * zeta[2 * k] * v**(2 * k - 1)
                             for k in range(1, (M - 1) // 2 + 1))
    for m in range(1, M + 1):
        actual = sp.expand(cotangent**m).coeff(v, -1) / sp.factorial(m)
        expected = (sp.S.Zero if m % 2 == 0 else
                    (-1)**((m + 1) // 2) * sp.pi**(m - 1) / sp.factorial(m))
        check("universal_cotangent_residue_coefficient", actual, expected,
              reduce_even=True, degree=m)

    # Elementary harmonic polynomials, independently generated from their
    # logarithmic finite-product identity (Newton's identities).
    e_log = {r: (-1)**(r + 1) * H[r] / r for r in range(1, M)}
    elementary = exponential_coefficients(e_log, M - 1)
    defects = {
        1: sp.S.Zero,
        2: sp.S.Zero,
        3: sp.S.Zero,
        4: -4 * (zeta[3] - H[3]),
        5: (-20 * H[1] * (zeta[3] - H[3])
            + 5 * (zeta[2] - H[2])**2
            - 20 * zeta[2] * (zeta[2] - H[2])
            + 25 * (zeta[4] - H[4])),
    }
    residues = {}
    for m in range(1, M + 1):
        regular = H[1] - gamma + sum(
            (H[r + 1] + (-1)**(r + 1) * zeta[r + 1]) * v**r
            for r in range(1, max(1, m - 1)))
        # Direct Laurent composition is independent of the displayed
        # double-coefficient residue formula.
        direct = sp.expand(P[m].subs(Y, -1 / v + regular)).coeff(v, -1)
        residues[m] = sp.expand(direct)
        defect = direct + sp.factorial(m) * elementary[m - 1]
        check("scalar_residue_defect", defect, defects[m],
              reduce_even=(m == 5), degree=m)
        if m >= 2:
            # Assemble Gamma(1-t)exp(t*b+t*sum a_r*v^r) without ever
            # forming exp(-t/v), then apply the stated finite formula.
            finite_log = {1: sp.expand(regular + gamma)}
            finite_log.update({r: zeta[r] / r for r in range(2, m + 1)})
            finite_coeff = exponential_coefficients(finite_log, m)
            finite_residue = sp.factorial(m) * sum(
                sp.Rational((-1)**h, sp.factorial(h))
                * sp.expand(finite_coeff[m - h]).coeff(v, h - 1)
                for h in range(1, m + 1))
            check("finite_double_coefficient_residue", direct, finite_residue,
                  degree=m)

    # Independent differential-polynomial generator for C_m.
    h = {1: psi[0] + gamma}
    h.update({r: zeta[r] + (-1)**(r + 1) * psi[r - 1]
              / sp.factorial(r - 1) for r in range(2, M + 1)})
    C_coeff = exponential_coefficients({r: h[r] / r for r in h}, M)
    C = [sp.expand(sp.factorial(m) * C_coeff[m]) for m in range(M + 1)]
    h1, h2, h3, h4, h5 = (h[r] for r in range(1, 6))
    displayed_C_Bell = {
        0: sp.S.One,
        1: h1,
        2: h1**2 + h2,
        3: h1**3 + 3 * h1 * h2 + 2 * h3,
        4: h1**4 + 6 * h1**2 * h2 + 3 * h2**2 + 8 * h1 * h3 + 6 * h4,
        5: (h1**5 + 10 * h1**3 * h2 + 15 * h1 * h2**2
            + 20 * h1**2 * h3 + 20 * h2 * h3 + 30 * h1 * h4 + 24 * h5),
    }
    for m, expected in displayed_C_Bell.items():
        check("displayed_complete_harmonic_Bell_polynomial", C[m], expected,
              degree=m)
    for m in range(M):
        recurrence = sum(sp.binomial(m, r) * sp.factorial(r) * h[r + 1]
                         * C[m - r] for r in range(m + 1))
        check("normalized_Gamma_finite_recurrence", C[m + 1], recurrence,
              degree=m + 1)
    Ppsi = [polynomial.subs(Y, psi[0]) for polynomial in P]
    displayed_C_differential = {
        2: Ppsi[2] - psi[1],
        3: Ppsi[3] - 3 * Ppsi[1] * psi[1] + psi[2],
        4: (Ppsi[4] - 6 * Ppsi[2] * psi[1] + 4 * Ppsi[1] * psi[2]
            - psi[3] + 3 * psi[1]**2),
        5: (Ppsi[5] - 10 * Ppsi[3] * psi[1] + 10 * Ppsi[2] * psi[2]
            - 5 * Ppsi[1] * psi[3] + 15 * Ppsi[1] * psi[1]**2
            - 10 * psi[1] * psi[2] + psi[4]),
    }
    for m, expected in displayed_C_differential.items():
        check("displayed_scalar_differential_comparison", C[m], expected,
              degree=m)

    # Inverse-Gamma derivatives, checked by formal differentiation and by
    # a separately assembled exponential generating function.
    def derivative(expr):
        return sp.expand(sum(sp.diff(expr, psi[r]) * psi[r + 1]
                             for r in range(M)))

    A = [sp.S.One]
    for m in range(M):
        A.append(sp.expand(psi[0] * A[-1] - derivative(A[-1])))
    a_log = {r: (-1)**(r + 1) * psi[r - 1] / sp.factorial(r)
             for r in range(1, M + 1)}
    a_coeff = exponential_coefficients(a_log, M)
    for m in range(M + 1):
        check("inverse_Gamma_derivative_recurrence_vs_generator",
              A[m], sp.factorial(m) * a_coeff[m], degree=m)
    displayed_A = {
        1: psi[0],
        2: psi[0]**2 - psi[1],
        3: psi[0]**3 - 3 * psi[0] * psi[1] + psi[2],
        4: (psi[0]**4 - 6 * psi[0]**2 * psi[1] + 3 * psi[1]**2
            + 4 * psi[0] * psi[2] - psi[3]),
        5: (psi[0]**5 - 10 * psi[0]**3 * psi[1] + 15 * psi[0] * psi[1]**2
            + 10 * psi[0]**2 * psi[2] - 10 * psi[1] * psi[2]
            - 5 * psi[0] * psi[3] + psi[4]),
    }
    for m, expected in displayed_A.items():
        check("displayed_inverse_Gamma_derivative_polynomial", A[m], expected,
              degree=m)

    # Reciprocal-Gamma c_n coefficients to a higher finite degree.
    c_log = {1: gamma}
    c_log.update({r: (-1)**(r + 1) * zeta[r] / r for r in range(2, N + 1)})
    c = exponential_coefficients(c_log, N)
    for n in range(1, N + 1):
        recurrence = (gamma * c[n - 1]
                      + sum((-1)**(r + 1) * zeta[r] * c[n - r]
                            for r in range(2, n + 1)))
        check("reciprocal_Gamma_coefficient_recurrence", n * c[n], recurrence,
              degree=n)
    for m in range(M + 1):
        convolution = sum(sp.factorial(m) / sp.factorial(k)
                          * (-1)**(m - k) * c[m - k] * C[k]
                          for k in range(m + 1))
        check("inverse_Gamma_C_convolution", A[m], convolution, degree=m)

    # The finite-part endpoints are supplied by the article's proof:
    # integral C0=1, FP integral C1=gamma, and integral Ck=k!(c_k-lambda_{k-1}).
    # We verify the whole resulting convolution with these two exceptional
    # entries retained.  The lambda_d remain independent formal symbols.
    log_v = sp.Symbol("log_v")
    log_Gamma_at_origin = (-log_v - gamma * v
                           + sum((-1)**r * zeta[r] * v**r / r
                                 for r in range(2, M + 1)))
    psi_cutoff_integral = -log_Gamma_at_origin
    endpoint_constant = sp.expand(psi_cutoff_integral).coeff(v, 0).coeff(log_v, 0)
    check("finite_part_psi_endpoint_constant", endpoint_constant, 0, degree=1)
    C1_cutoff_integral = psi_cutoff_integral + gamma * (1 - v)
    endpoint_constant = sp.expand(C1_cutoff_integral).coeff(v, 0).coeff(log_v, 0)
    check("finite_part_C1_endpoint_constant", endpoint_constant, gamma, degree=1)
    C_integrals = {0: sp.S.One, 1: gamma}
    C_integrals.update({k: sp.factorial(k) * (c[k] - lam[k - 1])
                       for k in range(2, N + 1)})

    def sinc_coefficient(m):
        if m % 2:
            return sp.S.Zero
        k = m // 2
        return (-1)**k * sp.pi**m / sp.factorial(m + 1)

    finite_parts = {}
    for m in range(N + 1):
        gamma_product = sum((-1)**(m - k) * c[m - k] * c[k]
                            for k in range(m + 1))
        check("reciprocal_Gamma_reflection_convolution", gamma_product,
              sinc_coefficient(m), reduce_even=True, degree=m)
        if m == 0:
            continue
        convolved_integral = sum(sp.factorial(m) / sp.factorial(k)
                                 * (-1)**(m - k) * c[m - k] * C_integrals[k]
                                 for k in range(m + 1))
        target = (sp.factorial(m) * sinc_coefficient(m)
                  - sp.factorial(m) * sum((-1)**(m - d - 1) * c[m - d - 1]
                                         * lam[d] for d in range(1, m)))
        check("all_degree_finite_part_convolution", convolved_integral,
              target, reduce_even=True, degree=m)
        if m <= M:
            finite_parts[m] = sp.expand(target)
    displayed_A5_integral = (
        -120 * lam[4] + 120 * gamma * lam[3]
        - 60 * (gamma**2 - zeta[2]) * lam[2]
        + 20 * (gamma**3 - 3 * gamma * zeta[2] + 2 * zeta[3]) * lam[1])
    check("displayed_fifth_inverse_Gamma_finite_part", finite_parts[5],
          displayed_A5_integral, degree=5)

    category_counts = {}
    for item in checks:
        name = item["name"]
        category_counts[name] = category_counts.get(name, 0) + 1
    report = {
        "status": "passed",
        "arithmetic": "exact symbolic rational-polynomial arithmetic; no numeric samples",
        "scope": {
            "scalar_defects_checked_through_degree": M,
            "differential_polynomials_checked_through_degree": M,
            "inverse_Gamma_differential_convolution_checked_through_degree": M,
            "reciprocal_Gamma_reflection_convolution_checked_through_degree": N,
            "finite_part_convolution_checked_through_degree": N,
            "analytic_or_all_degree_proof": False,
            "analytic_proofs": "See the article; the finite checks are supplementary.",
            "formal_symbols": {
                "gamma": "Euler constant",
                "zetaR": "zeta(R)",
                "HR": "H_n^(R), with H1=H_n",
                "psiR": "R-th x derivative of psi(x), with psi0=psi(x)",
                "lambdaD": "literal coefficient [u] Z_D(1+u,1,...,1)",
            },
            "only_special_value_reductions": {
                str(symbol): str(value) for symbol, value in even_zeta.items()
            },
            "finite_part_input": {
                "C0": "1",
                "C1": "gamma",
                "Ck_k_at_least_2": "k!*(c_k-lambda_(k-1))",
                "cutoff_coordinate": "x itself; no change of cutoff variable",
            },
        },
        "check_count": len(checks),
        "category_counts": category_counts,
        "checks": checks,
        "exact_outputs": {
            "P_m": {str(m): str(P[m]) for m in range(1, M + 1)},
            "scalar_residues": {str(m): str(residues[m]) for m in residues},
            "scalar_defects": {str(m): str(defects[m]) for m in defects},
            "A_m": {str(m): str(A[m]) for m in range(1, M + 1)},
            "finite_part_integrals_A_m": {
                str(m): str(finite_parts[m]) for m in finite_parts
            },
        },
        "versions": {"python": platform.python_version(), "sympy": sp.__version__},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "exact_checks": len(checks),
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
