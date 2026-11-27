#!/usr/bin/env python3
"""Reproduce exact algebra and floating-point checks for zero transport.

Run from any directory:
    python code/verify_transport.py

Dependencies: Python 3.10+, SymPy, mpmath.  The default output is
../data/verification.json relative to this script.

Exact checks use rational polynomial arithmetic and real-root isolation.
All transcendental/numerical checks use mpmath floating point; they are
diagnostics, NOT interval certificates and NOT proofs of RH or GRH.
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
from pathlib import Path

import mpmath as mp
import sympy as sp


Z = sp.Symbol("z")
LAM = sp.Symbol("lambda")
A_EXACT = sp.Matrix([[1, -1, 0], [-1, 2, -1], [0, -1, 1]])
V_EXACT = sp.Matrix([1, 0, -1])
B_EXACT = V_EXACT * V_EXACT.T
TR_B = int(sp.trace(B_EXACT))
ROOT_EPS = sp.Rational(1, 10**65)


def mpr(value):
    """Convert an exact rational to mpmath without passing through float."""
    value = sp.Rational(value)
    return mp.mpf(int(value.p)) / int(value.q)


def number(value, digits=45):
    if isinstance(value, mp.mpc):
        return {"re": mp.nstr(value.real, digits), "im": mp.nstr(value.imag, digits)}
    return mp.nstr(value, digits)


def mp_matrix(matrix):
    return mp.matrix([[mpr(matrix[i, j]) for j in range(matrix.cols)]
                      for i in range(matrix.rows)])


def trace(matrix):
    return sum(matrix[i, i] for i in range(matrix.rows))


def inf_norm(matrix):
    return max(sum(abs(matrix[i, j]) for j in range(matrix.cols))
               for i in range(matrix.rows))


def principal_minor_polynomial(functions, coupling):
    """Entire extension of prod(F_i) det(A+diag(F_i'/F_i))."""
    n = len(functions)
    answer = sp.Integer(0)
    for size in range(n + 1):
        for subset in itertools.combinations(range(n), size):
            minor = coupling.extract(subset, subset).det() if subset else sp.Integer(1)
            answer += minor * sp.prod(functions[j] if j in subset
                                      else sp.diff(functions[j], Z) for j in range(n))
    return sp.Poly(sp.expand(answer), Z)


def isolate(poly):
    """Sturm-based rational intervals certify all real roots with multiplicity."""
    entries = []
    for (lo, hi), multiplicity in poly.intervals(eps=ROOT_EPS):
        entries.append({"lo": lo, "hi": hi, "multiplicity": multiplicity,
                        "mid": (mpr(lo) + mpr(hi)) / 2})
    assert sum(item["multiplicity"] for item in entries) == poly.degree()
    return entries


def evaluate_poly(poly, value):
    return mp.polyval([mpr(c) for c in poly.all_coeffs()], value)


def sample_between(left, right, functions):
    middle = (mpr(left) + mpr(right)) / 2
    candidate = sp.Rational(int(mp.nint(middle * 10**8)), 10**8)
    if not left < candidate < right or any(f.subs(Z, candidate) == 0 for f in functions):
        for denominator in range(2, 20):
            candidate = ((denominator - 1) * left + right) / denominator
            if all(f.subs(Z, candidate) != 0 for f in functions):
                break
        else:
            raise AssertionError("Could not choose a regular sample")
    return candidate


def positive_inertia(matrix):
    assert matrix.det() != 0
    characteristic = sp.Poly(matrix.charpoly(LAM).as_expr(), LAM)
    # SymPy's real count_roots counts distinct roots.  Restore algebraic
    # multiplicities, essential for the repeated-input/triangle example.
    return sum(int(multiplicity) * int(factor.count_roots(0, sp.oo))
               for factor, multiplicity in sp.factor_list(characteristic)[1])


def exact_polynomial_case(name, functions):
    functions = [sp.expand(f) for f in functions]
    p0 = principal_minor_polynomial(functions, A_EXACT)
    p1 = principal_minor_polynomial(functions, A_EXACT + B_EXACT)
    diagonal = sp.diag(*[sp.diff(f, Z) / f for f in functions])
    determinant_expression0 = sp.cancel(sp.prod(functions) * (A_EXACT + diagonal).det())
    determinant_expression1 = sp.cancel(sp.prod(functions) * (A_EXACT + B_EXACT + diagonal).det())
    assert sp.cancel(determinant_expression0 - p0.as_expr()) == 0
    assert sp.cancel(determinant_expression1 - p1.as_expr()) == 0
    roots0, roots1 = isolate(p0), isolate(p1)
    common = sp.gcd(p0, p1)
    q0, q1 = p0.exquo(common), p1.exquo(common)
    alpha, beta = isolate(q0), isolate(q1)
    assert len(alpha) == len(beta)
    assert all(r["multiplicity"] == 1 for r in alpha + beta)
    assert all(alpha[k]["hi"] < beta[k]["lo"] for k in range(len(alpha)))
    assert all(beta[k]["hi"] < alpha[k + 1]["lo"] for k in range(len(alpha) - 1))

    # Exact inertia comparisons at regular rational samples, including gaps.
    inertia_samples = []
    boundary_pairs = []
    boundary_pairs.append((alpha[0]["lo"] - 1, alpha[0]["lo"], 0))
    for k in range(len(alpha)):
        boundary_pairs.append((alpha[k]["hi"], beta[k]["lo"], 1))
        if k + 1 < len(alpha):
            boundary_pairs.append((beta[k]["hi"], alpha[k + 1]["lo"], 0))
    boundary_pairs.append((beta[-1]["hi"], beta[-1]["hi"] + 1, 0))
    for left, right, expected in boundary_pairs:
        x = sample_between(left, right, functions)
        m0 = A_EXACT + diagonal.subs(Z, x)
        xi = positive_inertia(m0 + B_EXACT) - positive_inertia(m0)
        assert xi == expected
        inertia_samples.append({"x_exact": str(x), "xi_exact": xi})

    poisson_rows = []
    for y in map(mp.mpf, ["0.3", "1", "3", "10"]):
        ratio = evaluate_poly(p1, mp.j * y) / evaluate_poly(p0, mp.j * y)
        from_log = y * mp.im(mp.log(ratio))
        from_roots = y * sum(mp.atan(b["mid"] / y) - mp.atan(a["mid"] / y)
                             for a, b in zip(alpha, beta))
        from_quadrature = sum(mp.quad(lambda x: y*y/(x*x+y*y), [a["mid"], b["mid"]])
                              for a, b in zip(alpha, beta))
        error = max(abs(from_log - from_roots), abs(from_log - from_quadrature))
        assert error < mp.mpf("1e-55")
        poisson_rows.append({"y": number(y), "y_im_log_ratio": number(from_log),
                             "root_arctangent_sum": number(from_roots),
                             "interval_quadrature": number(from_quadrature),
                             "max_absolute_discrepancy": number(error)})

    return {
        "name": name,
        "inputs_exact": [str(f) for f in functions],
        "P_A_exact": str(p0.as_expr()),
        "P_A_plus_B_exact": str(p1.as_expr()),
        "common_factor_exact": str(common.as_expr()),
        "degrees": [p0.degree(), p1.degree()],
        "real_root_multiplicities": [[r["multiplicity"] for r in roots0],
                                     [r["multiplicity"] for r in roots1]],
        "entire_extension_identity_exact": True,
        "all_roots_real_sturm_certificate": True,
        "simple_strict_interlacing_after_cancellation_exact": True,
        "paired_roots_approx": [[number(a["mid"]), number(b["mid"])]
                                for a, b in zip(alpha, beta)],
        "rational_isolating_intervals_after_cancellation": {
            "old": [[str(r["lo"]), str(r["hi"])] for r in alpha],
            "new": [[str(r["lo"]), str(r["hi"])] for r in beta]},
        "exact_inertia_samples": inertia_samples,
        "poisson_identity_floating_checks": poisson_rows,
    }


def character_value(q, n):
    if q == 1:
        return 1
    if q == 3:
        return (0, 1, -1)[n % 3]
    if q == 4:
        return (0, 1, 0, -1)[n % 4]
    raise ValueError("Only conductors 1, 3, 4 are used by this diagnostic")


def completed_log_derivative(q, y, terms=64):
    """D_q(y) with g_q(iy)=-i D_q(y), computed at sigma=y+1/2>1.

    Integral comparison gives explicit tails for L and L'.  Evaluation
    itself is floating point, so these are estimates, not certificates.
    """
    sigma = y + mp.mpf("0.5")
    parity = 0 if q == 1 else 1
    l_value = mp.mpf(0)
    l_derivative = mp.mpf(0)
    for n in range(1, terms + 1):
        chi = character_value(q, n)
        if chi:
            term = chi * mp.exp(-sigma * mp.log(n))
            l_value += term
            l_derivative -= mp.log(n) * term
    e0 = mp.power(terms, 1 - sigma) / (sigma - 1)
    e1 = mp.power(terms, 1 - sigma) * (mp.log(terms)/(sigma - 1) + 1/(sigma - 1)**2)
    assert abs(l_value) > e0
    ratio_tail = e1/(abs(l_value) - e0) + abs(l_derivative)*e0/(abs(l_value)*(abs(l_value) - e0))
    value = mp.log(mp.mpf(q)/mp.pi)/2 + mp.digamma((sigma + parity)/2)/2 + l_derivative/l_value
    if q == 1:
        value += 1/sigma + 1/(sigma - 1)  # xi(s) has s(s-1)/2.
    return value, ratio_tail


def trace_log_series(h0, h1, ell, order):
    p0 = mp.eye(h0.rows)
    p1 = mp.eye(h1.rows)
    answer = mp.mpc(0)
    ell_power = mp.mpf(1)
    for k in range(1, order + 1):
        p0 = p0 * h0
        p1 = p1 * h1
        ell_power *= ell
        answer += (-1)**(k + 1) * (trace(p1) - trace(p0)) / (k * ell_power)
    return answer


def dirichlet_asymptotic_checks(log_ys):
    a = mp_matrix(A_EXACT)
    b = mp_matrix(B_EXACT)
    c = mp.diag([mp.log(mp.mpf(q)/(2*mp.pi))/2 for q in (1, 3, 4)])
    h0, h1 = c + mp.j*a, c + mp.j*(a+b)
    norm0, norm1 = inf_norm(h0), inf_norm(h1)
    rows, squared_rows = [], []
    for log_y in log_ys:
        y = mp.exp(log_y)
        ell = mp.mpf(log_y)/2
        ds_and_tails = [completed_log_derivative(q, y) for q in (1, 3, 4)]
        ds = [v for v, _ in ds_and_tails]
        m0 = a - mp.j * mp.diag(ds)
        m1 = m0 + b
        exact_f = mp.log(mp.det(m1)/mp.det(m0))
        limit_f = mp.log(mp.det(ell*mp.eye(3)+h1)/mp.det(ell*mp.eye(3)+h0))
        assert 0 < mp.im(exact_f) < mp.pi
        cubic_f = trace_log_series(h0, h1, ell, 3)
        row = {
            "log_y": log_y,
            "y": number(y),
            "D_conductors_1_3_4": list(map(number, ds)),
            "log10_max_Lprime_over_L_tail_estimate": number(max(mp.log10(t) for _, t in ds_and_tails)),
            "max_D_minus_half_log_y_minus_C": number(max(abs(ds[i]-ell-c[i,i]) for i in range(3))),
            "normalized_y_im_f": number(ell*mp.im(exact_f)/TR_B),
            "normalized_three_term_expansion": number(ell*mp.im(cubic_f)/TR_B),
            "actual_f": number(exact_f),
            "limit_model_f": number(limit_f),
            "abs_actual_minus_limit_model": number(abs(exact_f-limit_f)),
        }
        if ell > max(norm0, norm1):
            order = 96
            approximation = trace_log_series(h0, h1, ell, order)
            rho0, rho1 = norm0/ell, norm1/ell
            remainder = 3/(order+1) * (rho0**(order+1)/(1-rho0) + rho1**(order+1)/(1-rho1))
            row.update({"convergent_series_order": order,
                        "normalized_high_order_expansion": number(ell*mp.im(approximation)/TR_B),
                        "series_vs_limit_model_absolute_error": number(abs(approximation-limit_f)),
                        "geometric_remainder_bound_formula_value": number(remainder)})
            assert abs(approximation-limit_f) <= remainder + mp.mpf("1e-160")
        else:
            row.update({"convergent_series_order": None,
                        "series_note": "The sufficient norm condition fails here; no convergent-series remainder is claimed."})
        rows.append(row)

        # All-three-zeta squared-variable graph example.
        # R=y^2, m(-R)=-D_zeta(y)/(2y), tau0=1, tau1=3.
        m = -ds[0]/(2*y)
        # Stable log evaluation is essential when log_y is 100 or 200.
        graph_log = mp.log1p(m/3) - mp.log1p(m)
        normalized_graph_log = graph_log*y/(2*log_y)
        squared_rows.append({"log_y": log_y, "log_R": 2*log_y,
                             "m_minus_R": number(m),
                             "normalized_log_ratio_sqrt_R_over_log_R": number(normalized_graph_log),
                             "predicted_limit_one_twelfth": number(mp.mpf(1)/12),
                             "ratio_to_predicted_limit": number(12*normalized_graph_log)})
    return {
        "conductors": [1, 3, 4],
        "parities": [0, 1, 1],
        "direct_Dirichlet_series_terms": 64,
        "definition_of_normalized_y_im_f": "(log y)/(2 tr B) Im log(det(M_A+B)/det(M_A)); expected limit 1",
        "three_term_and_high_order_formula": "sum_{k=1}^K (-1)^(k+1) [tr(H1^k)-tr(H0^k)]/(k ell^k), ell=log(y)/2, Hj=C+i Aj",
        "C_diagonal": [number(c[i,i]) for i in range(3)],
        "rows": rows,
    }, squared_rows


def squared_graph_exact_checks():
    m = sp.Symbol("m")
    identity = sp.eye(3)
    tau0 = A_EXACT[:2,:2].det()
    tau1 = (A_EXACT+B_EXACT)[:2,:2].det()
    ratio = sp.factor(((A_EXACT+B_EXACT+m*identity).det()/tau1)
                      / ((A_EXACT+m*identity).det()/tau0))
    assert sp.cancel(ratio - (m+3)/(3*(m+1))) == 0
    assert tau0 == 1 and tau1 == 3
    # Kirchhoff index K=n tr(L^+), exact rational pseudoinverse.
    k0 = sp.simplify(3*sp.trace(A_EXACT.pinv()))
    k1 = sp.simplify(3*sp.trace((A_EXACT+B_EXACT).pinv()))
    assert k0 == 4 and k1 == 2
    return {"tau_path_exact": int(tau0), "tau_triangle_exact": int(tau1),
            "Kirchhoff_path_exact": int(k0), "Kirchhoff_triangle_exact": int(k1),
            "Delta_K_exact": int(k0-k1), "normalized_ratio_exact": str(ratio),
            "asymptotic_log_ratio_coefficient_exact": str((k0-k1)/(8*3)),
            "predicted_squared_displacement_coefficient": "1/(6*pi)",
            "predicted_positive_ordinate_displacement_coefficient": "1/(12*pi)",
            "central_zero_note": "The numerical squared example uses three copies of Xi; zeta(1/2) is nonzero, so no central-zero removal is needed."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"data"/"verification.json")
    parser.add_argument("--dps", type=int, default=180)
    args = parser.parse_args()
    mp.mp.dps = args.dps
    if args.dps < 110:
        raise SystemExit("Use at least 110 decimal digits for the log_y=200 squared diagnostic.")
    generic = [(Z+2)*(Z-1)**2, (Z+2)*(Z-3), Z*(Z-1)*(Z+4)]
    repeated = [(Z**2-1)**2]*3
    polynomial_checks = [exact_polynomial_case("asymmetric_shared_and_repeated_roots", generic),
                         exact_polynomial_case("three_identical_repeated_inputs", repeated)]
    analytic_checks, squared_rows = dirichlet_asymptotic_checks([5, 10, 20, 50, 100, 200])
    squared = squared_graph_exact_checks()
    squared["floating_checks"] = squared_rows
    result = {
        "artifact": "dirichlet_zero_transport verification",
        "status": "All programmed assertions passed. Floating-point output is diagnostic, not a proof certificate.",
        "versions": {"python": platform.python_version(), "sympy": sp.__version__,
                     "mpmath": mp.__version__, "decimal_precision": args.dps},
        "A_path_exact": A_EXACT.tolist(), "B_edge_13_exact": B_EXACT.tolist(),
        "rank_B_exact": int(B_EXACT.rank()), "trace_B_exact": TR_B,
        "exact_polynomial_checks": polynomial_checks,
        "Dirichlet_imaginary_axis_checks": analytic_checks,
        "squared_graph_checks": squared,
        "limitations": [
            "No RH or GRH assertion is checked by numerical zeros.",
            "Sturm root isolation and rational identities are exact; mpmath calculations are not rigorously rounded.",
            "The finite Dirichlet-series tail formula controls truncation analytically, but its reported numerical evaluation is not an interval certificate.",
            "The asymptotic checks inspect positive real Laplace/Stieltjes arguments; they do not replace the Tauberian proof of unsmoothed transport.",
            "High-order expansions are compared with the large-y limit matrix; finite-y digamma errors are reported separately.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, default=lambda obj: int(obj) if isinstance(obj, sp.Integer) else str(obj))+"\n")
    print("Exact polynomial identities, root isolation, interlacing and inertia samples: PASS")
    print("Poisson/arctangent checks: PASS")
    print("log(y) | normalized y Im f | normalized squared ratio / (1/12)")
    for first, second in zip(analytic_checks["rows"], squared_rows):
        print(f"{first['log_y']:6d} | {first['normalized_y_im_f'][:18]:>18} | {second['ratio_to_predicted_limit'][:18]:>18}")
    print(f"Saved {args.output}")


if __name__ == "__main__":
    main()
