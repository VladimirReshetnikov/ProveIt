#!/usr/bin/env python3
"""Reproduce exact algebraic checks and illustrations for reciprocal-zero bounds.

Run from any directory:
    python verify_reciprocal_bounds.py
    python verify_reciprocal_bounds.py --output-dir /path/to/output

Dependencies: Python >= 3.10, sympy, mpmath, matplotlib.

The rational and symbolic checks verify specific identities and a finite sample
of the square-prefix optimizer. They do not replace the proofs in the paper.
The plots evaluate proved bound formulas; they do not estimate the unknown
optimal zero-free interval for square spectra.

Conventions:
    Fourier frequencies a use exp(2*pi*i*a*x) on R/Z.
    H is the number of square frequencies, indexed n=N,...,N+H-1.
    b(N,m) = m^2 / (2*sum_{n=N}^{N+m-1} n^2).
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import platform
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import sympy as sp


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def decimal(value: Fraction | sp.Expr | mp.mpf, digits: int = 40) -> str:
    if isinstance(value, Fraction):
        value = mp.mpf(value.numerator) / value.denominator
    elif isinstance(value, sp.Expr):
        value = mp.mpf(str(sp.N(value, mp.mp.dps)))
    return mp.nstr(value, digits)


def symbolic_checks() -> dict:
    N, m = sp.symbols("N m", integer=True, positive=True)
    j = sp.symbols("j", integer=True, nonnegative=True)
    u = sp.symbols("u", positive=True)
    direct_sum = sp.summation((N + j) ** 2, (j, 0, m - 1))
    D = 2 * m**2 + (6 * N - 3) * m + 6 * N**2 - 6 * N + 1
    closed_sum = m * D / 6
    assert sp.simplify(direct_sum - closed_sum) == 0
    b = 3 * m / D
    assert sp.simplify(m**2 / (2 * direct_sum) - b) == 0
    difference = 3 * (6 * N**2 - 6 * N + 1 - 2 * m * (m + 1))
    difference /= D * D.subs(m, m + 1)
    assert sp.simplify(b.subs(m, m + 1) - b - difference) == 0
    g = 3 * u / (2 * (u**2 + 3 * u + 3))
    derivative = 3 * (3 - u**2) / (2 * (u**2 + 3 * u + 3) ** 2)
    assert sp.simplify(sp.diff(g, u) - derivative) == 0
    plateau = sp.sqrt(3) - sp.Rational(3, 2)
    assert sp.simplify(g.subs(u, sp.sqrt(3)) - plateau) == 0
    odd_zeta = sp.summation(1 / (2 * j + 1) ** 2, (j, 0, sp.oo))
    assert sp.simplify(odd_zeta - sp.pi**2 / 8) == 0
    x, t, p = sp.symbols("x t p", positive=True)
    hinge_integral = sp.integrate((t - x) * t ** (-p - 2), (t, x, sp.oo))
    assert sp.simplify(p * (p + 1) * hinge_integral - x ** (-p)) == 0
    return {
        "sum_of_squares_identity": str(closed_sum),
        "square_prefix_bound": str(b),
        "successive_difference": str(sp.factor(difference)),
        "no_tie_reason": (
            "6*N^2-6*N+1 is odd, while 2*m*(m+1) is even; "
            "the successive difference cannot vanish for integer N,m."
        ),
        "unrestricted_optimizer": "floor((1 + sqrt(12*N^2-12*N+1))/2)",
        "restricted_optimizer": "min(H, floor((1 + sqrt(12*N^2-12*N+1))/2))",
        "integer_implementation": "min(H, (1+isqrt(12*N*N-12*N+1))//2)",
        "equivalent_alternative_optimizer": "floor((1 + sqrt(12*N^2-12*N+3))/2)",
        "equivalence_reason": (
            "Let A=3*N*(N-1), an integer. The unique unrestricted maximizing m satisfies "
            "m*(m-1)<=A<m*(m+1), giving the canonical discriminant 4*A+1. "
            "The floor of (1+sqrt(D))/2 increases only when D reaches an odd square, "
            "which is 1 modulo 4. There is no odd square in (4*A+1,4*A+3], "
            "so replacing the discriminant +1 by +3 leaves this floor unchanged."
        ),
        "asymptotic_lower_envelope": str(g),
        "asymptotic_lower_derivative": str(derivative),
        "asymptotic_lower_plateau": str(plateau),
        "odd_inverse_square_sum": str(odd_zeta),
        "hinge_integral_identity": "p*(p+1)*integral_x^infinity (t-x)*t^(-p-2) dt = x^(-p)",
        "status": "All listed symbolic identities verified exactly by SymPy.",
    }


def square_optimizer_checks(output_dir: Path) -> dict:
    """Compare the derived optimizer with independently enumerated rationals."""
    rows: list[dict] = []
    optimizer_ties = 0
    checked_prefixes = 0
    for N in range(1, 101):
        max_H = 4 * N + 10
        unrestricted_canonical = (1 + math.isqrt(12 * N * N - 12 * N + 1)) // 2
        unrestricted_alternative = (1 + math.isqrt(3 * (2 * N - 1) ** 2)) // 2
        assert unrestricted_canonical == unrestricted_alternative, N
        prefix_bounds: list[Fraction] = []
        running_sum = 0
        for m in range(1, max_H + 1):
            running_sum += (N + m - 1) ** 2
            direct = Fraction(m * m, 2 * running_sum)
            formula = Fraction(
                3 * m,
                2 * m * m + (6 * N - 3) * m + 6 * N * N - 6 * N + 1,
            )
            assert direct == formula, (N, m)
            prefix_bounds.append(direct)
        for H in range(1, max_H + 1):
            # Exhaustive comparison with exact rational arithmetic. This code
            # deliberately does not use the successive-difference formula.
            best = max(prefix_bounds[:H])
            maximizers = [m + 1 for m, b in enumerate(prefix_bounds[:H]) if b == best]
            m_formula = min(H, unrestricted_canonical)
            m_alternative = min(H, unrestricted_alternative)
            optimizer_ties += int(len(maximizers) != 1)
            assert maximizers == [m_formula], (N, H, maximizers, m_formula)
            assert maximizers == [m_alternative], (N, H, maximizers, m_alternative)
            upper = sum((Fraction(1, 2 * n * n) for n in range(N, N + H)), Fraction())
            assert best <= upper
            rows.append({
                "N": N,
                "H": H,
                "enumerated_optimal_prefix_m": maximizers[0],
                "closed_form_optimal_prefix_m": m_formula,
                "alternative_plus_three_optimal_prefix_m": m_alternative,
                "number_of_maximizers": len(maximizers),
                "lower_bound_numerator": best.numerator,
                "lower_bound_denominator": best.denominator,
                "lower_bound_decimal": decimal(best, 25),
                "upper_bound_numerator": upper.numerator,
                "upper_bound_denominator": upper.denominator,
                "upper_bound_decimal": decimal(upper, 25),
            })
            checked_prefixes += 1
    assert checked_prefixes == 21_200
    assert optimizer_ties == 0
    write_csv(output_dir / "square_prefix_checks.csv", rows)
    return {
        "N_range": [1, 100],
        "H_range_for_each_N": "1 <= H <= 4*N+10",
        "cases_checked": checked_prefixes,
        "optimizer_ties": optimizer_ties,
        "all_closed_form_optimizers_match_exact_enumeration": True,
        "canonical_plus_one_and_alternative_plus_three_formulas_agree": True,
        "all_exact_lower_bounds_do_not_exceed_Kozma_Oravecz_upper_bounds": True,
        "interpretation": (
            "The optimizer is that of the proved prefix lower bound, "
            "not necessarily the actual maximum zero-free interval. "
            "The algebraic sign formula in the paper proves the result for all N,H; "
            "this finite enumeration is an independent consistency check."
        ),
        "csv": "square_prefix_checks.csv",
    }


def finite_constant_checks(output_dir: Path) -> dict:
    sample_n = {1, 2, 3, 4, 5, 10, 20, 50, 100, 200, 500, 1000}
    rows: list[dict] = []
    odd_sum = Fraction()
    c_infinity = 1 / (mp.sqrt(2) * mp.pi)
    previous = mp.inf
    for n in range(1, max(sample_n) + 1):
        old_sum = odd_sum
        odd_sum += Fraction(1, (2 * n - 1) ** 2)
        assert odd_sum > old_sum
        root = mp.sqrt(mp.mpf(odd_sum.numerator) / odd_sum.denominator)
        c_n = 1 / (4 * root)
        assert c_n < previous and c_n > c_infinity
        previous = c_n
        if n in sample_n:
            epsilon = Fraction(1, 100 * n)
            outer_radius = Fraction(1, 4) + epsilon
            rows.append({
                "n": n,
                "odd_square_sum_numerator": odd_sum.numerator,
                "odd_square_sum_denominator": odd_sum.denominator,
                "C_n": decimal(c_n),
                "C_infinity": decimal(c_infinity),
                "C_n_minus_C_infinity": decimal(c_n - c_infinity),
                "sharp_measure_radius": "1/4",
                "smooth_epsilon": str(epsilon),
                "smooth_admissible_outer_radius": str(outer_radius),
                "smooth_radius_divided_by_sqrt_sum": decimal(
                    (mp.mpf(outer_radius.numerator) / outer_radius.denominator) / root
                ),
            })
    write_csv(output_dir / "sharp_constants.csv", rows)
    return {
        "finite_constant": "C_n = 1/(4*sqrt(sum_{j=1}^n (2*j-1)^(-2)))",
        "universal_constant": "C_infinity = 1/(sqrt(2)*pi)",
        "universal_constant_decimal": decimal(c_infinity),
        "sharpness_for_measures": (
            "A_n={1,3,...,2*n-1}; mu=(delta_{-1/4}+delta_{1/4})/2. "
            "Its Fourier coefficient at integer a is cos(pi*a/2). "
            "The radius-to-reciprocal-norm ratio is exactly C_n."
        ),
        "sharpness_for_smooth_functions": (
            "Fix a nonnegative C-infinity probability density beta supported in [-1/2,1/2]. "
            "Set beta_epsilon(x)=epsilon^(-1)*beta(x/epsilon) and "
            "f_epsilon(x)=(beta_epsilon(x-1/4)+beta_epsilon(x+1/4))/2, periodized on R/Z. "
            "For 0<epsilon<1/2 its support lies strictly inside "
            "(-1/4-epsilon,1/4+epsilon). Its Fourier coefficients are "
            "cos(pi*a/2)*hat(beta_epsilon)(a), hence vanish at every odd a. "
            "As epsilon decreases to zero the ratio tends to C_n. "
            "Taking epsilon=1/(100*n) and n increasing shows the universal constant cannot be increased."
        ),
        "precision_decimal_digits": mp.mp.dps,
        "csv": "sharp_constants.csv",
    }


def bernstein_certificate(output_dir: Path) -> dict:
    u, t = sp.symbols("u t")
    Q = 5 * sp.chebyshevt(4, u) - 5 * sp.chebyshevt(9, u) + 2 * sp.chebyshevt(16, u)
    P = sp.Poly(Q.subs(u, sp.Rational(89, 100) + sp.Rational(11, 100) * t), t)
    degree = P.degree()
    power_coefficients = [P.nth(k) for k in range(degree + 1)]
    bernstein = [
        sp.factor(sum(
            power_coefficients[k] * sp.binomial(j, k) / sp.binomial(degree, k)
            for k in range(j + 1)
        ))
        for j in range(degree + 1)
    ]
    reconstruction = sum(
        bernstein[j] * sp.binomial(degree, j) * t**j * (1 - t) ** (degree - j)
        for j in range(degree + 1)
    )
    assert sp.Poly(sp.expand(reconstruction) - P.as_expr(), t).is_zero
    assert all(b > 0 for b in bernstein)
    minimum = min(bernstein)
    assert minimum == sp.Rational(1143, 1600)
    # Exact rational inequalities proving cos(3*pi/20)>89/100:
    assert sp.Rational(9, 4) ** 2 > 5
    assert sp.Rational(11, 2) > sp.Rational(117, 50) ** 2
    assert (4 + sp.Rational(117, 50)) / 8 == sp.Rational(317, 400)
    assert sp.Rational(317, 400) > sp.Rational(89, 100) ** 2
    trig_expression = (4 + sp.sqrt(10 - 2 * sp.sqrt(5))) / 8
    assert sp.simplify(sp.cos(3 * sp.pi / 20) ** 2 - trig_expression) == 0
    write_csv(output_dir / "bernstein_certificate.csv", [
        {
            "j": j,
            "degree": degree,
            "bernstein_coefficient_numerator": int(b.p),
            "bernstein_coefficient_denominator": int(b.q),
            "bernstein_coefficient_decimal": decimal(b, 25),
        }
        for j, b in enumerate(bernstein)
    ])
    return {
        "status": "Exact rational polynomial identity and all coefficient signs verified.",
        "trigonometric_polynomial": "5*cos(8*pi*x)-5*cos(18*pi*x)+2*cos(32*pi*x)",
        "spectrum": [-16, -9, -4, 4, 9, 16],
        "certified_interval": "[-3/40,3/40]",
        "interval_length": "3/20",
        "Chebyshev_polynomial": str(sp.expand(Q)),
        "substitution": "u = 89/100 + (11/100)*t, 0 <= t <= 1",
        "Bernstein_degree": degree,
        "minimum_Bernstein_coefficient": str(minimum),
        "exact_uniform_positive_lower_bound": str(minimum),
        "trigonometric_endpoint_certificate": (
            "cos(3*pi/20)^2=(4+sqrt(10-2*sqrt(5)))/8; "
            "sqrt(5)<9/4, hence sqrt(10-2*sqrt(5))>sqrt(11/2)>117/50; "
            "therefore cos(3*pi/20)^2>317/400>(89/100)^2."
        ),
        "interpretation": (
            "An illustrative explicit zero-free interval for one square spectrum. "
            "No claim that this polynomial or interval is extremal. "
            "The degree-16 Bernstein basis functions are nonnegative and sum to one on [0,1], "
            "so the exact certificate is a proof of the displayed positivity claim."
        ),
        "csv": "bernstein_certificate.csv",
    }


def make_figure(output_dir: Path) -> dict:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import ScalarFormatter

    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 10,
        "axes.titlesize": 11,
        "axes.labelsize": 10,
        "legend.fontsize": 9,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "pdf.fonttype": 42,
        "savefig.facecolor": "white",
    })
    blue, orange = "#155F88", "#C26221"
    fig, axes = plt.subplots(1, 2, figsize=(11.6, 4.45), layout="constrained")
    n_values = list(range(1, 1001))
    partial = 0.0
    constants = []
    for n in n_values:
        partial += 1.0 / (2 * n - 1) ** 2
        constants.append(1.0 / (4.0 * math.sqrt(partial)))
    c_inf = 1.0 / (math.sqrt(2.0) * math.pi)
    axes[0].plot(n_values, constants, color=blue, linewidth=2.2, label=r"Finite-set constant $C_n$")
    axes[0].axhline(c_inf, color=orange, linestyle="--", linewidth=1.8,
                   label=r"Optimal universal constant $1/(\sqrt{2}\,\pi)$")
    axes[0].set_xscale("log")
    axes[0].set_xticks([1, 2, 5, 10, 50, 100, 1000])
    axes[0].xaxis.set_major_formatter(ScalarFormatter())
    axes[0].set_xlim(1, 1000)
    axes[0].set_ylim(0.223, 0.252)
    axes[0].set_title("Sharp constants for finite target sets", loc="left", fontweight="bold")
    axes[0].set_xlabel("Number of prescribed frequencies n (logarithmic scale)")
    axes[0].set_ylabel(r"$C_n=1\,/\!\left(4\sqrt{\sum_{j=1}^n(2j-1)^{-2}}\right)$")
    axes[0].grid(axis="y", color="#DEE4E8", linewidth=0.7)
    axes[0].legend(loc="upper right", frameon=False)

    tau_values = [10 * j / 1000 for j in range(1001)]
    lower, upper = [], []
    for tau in tau_values:
        u = min(tau, math.sqrt(3))
        lower.append(3 * u / (2 * (u * u + 3 * u + 3)))
        upper.append(tau / (2 * (1 + tau)))
    axes[1].fill_between(tau_values, lower, upper, color="#EAF0F3", label="Region between the bounds")
    axes[1].plot(tau_values, lower, color=blue, linewidth=2.2, label="Proved asymptotic lower bound")
    axes[1].plot(tau_values, upper, color=orange, linewidth=2.2, label="Kozma–Oravecz upper bound")
    axes[1].axvline(math.sqrt(3), color="#7B858C", linestyle=":", linewidth=1.1)
    axes[1].text(math.sqrt(3) + 0.11, 0.025, r"$\sqrt{3}$", color="#606A72")
    axes[1].set_xlim(0, 10)
    axes[1].set_ylim(0, 0.5)
    axes[1].set_title("Bounds for square spectra", loc="left", fontweight="bold")
    axes[1].set_xlabel(r"Asymptotic ratio $\tau=H/N$")
    axes[1].set_ylabel(r"Bounds on $N\,M_{N,K}$")
    axes[1].grid(axis="y", color="#DEE4E8", linewidth=0.7)
    axes[1].legend(loc="lower right", frameon=False)
    fig.suptitle("Sharp support constants and bounds on zero-free intervals", fontsize=14, fontweight="bold")
    for suffix in ("pdf", "png"):
        fig.savefig(output_dir / f"reciprocal_bounds_figure.{suffix}", dpi=220)
    plt.close(fig)
    write_csv(output_dir / "square_asymptotic_bounds.csv", [
        {"tau": f"{tau:.8f}", "lower_bound": f"{lo:.16g}", "upper_bound": f"{hi:.16g}"}
        for tau, lo, hi in zip(tau_values, lower, upper)
    ])
    return {
        "files": ["reciprocal_bounds_figure.pdf", "reciprocal_bounds_figure.png"],
        "left_panel": "Sharp C_n and its universal limit; logarithmic n axis.",
        "right_panel": (
            "Lower 3*u/[2*(u^2+3*u+3)] with u=min(tau,sqrt(3)); "
            "upper tau/[2*(1+tau)]. Curves are bounds, not computed optima."
        ),
        "right_panel_data_csv": "square_asymptotic_bounds.csv",
        "matplotlib_version": matplotlib.__version__,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 70
    results = {
        "purpose": "Independent exact checks and illustrations accompanying the mathematical proof.",
        "limitations": (
            "Finite enumeration does not prove the universal theorem; numerical plots do not compute "
            "the extremal zero-free interval. The symbolic identities and exact Bernstein certificate "
            "have the explicit scopes stated below."
        ),
        "convention": "T=R/Z and Fourier exp(2*pi*i*a*x); H is number of square frequencies.",
        "versions": {
            "python": platform.python_version(),
            "sympy": sp.__version__,
            "mpmath": mp.__version__,
        },
        "symbolic_checks": symbolic_checks(),
        "square_optimizer_checks": square_optimizer_checks(output_dir),
        "sharp_constants": finite_constant_checks(output_dir),
        "illustrative_exact_positivity_certificate": bernstein_certificate(output_dir),
        "figure": make_figure(output_dir),
    }
    (output_dir / "verification_results.json").write_text(
        json.dumps(results, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(json.dumps({
        "status": "All checks passed.",
        "square_optimizer_cases": results["square_optimizer_checks"]["cases_checked"],
        "optimizer_ties": results["square_optimizer_checks"]["optimizer_ties"],
        "exact_Bernstein_minimum": results["illustrative_exact_positivity_certificate"]["minimum_Bernstein_coefficient"],
        "output_dir": str(output_dir),
    }, indent=2))


if __name__ == "__main__":
    main()
