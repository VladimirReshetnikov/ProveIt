#!/usr/bin/env python3
"""
Reproducible symbolic and numerical experiments for
"Dyadic Stein--Koopman Calculus for the Fabius--Rvachev Law".

The script has four goals.

1. Construct the centered Rvachev moments from their Bernoulli cumulants,
   then construct the reciprocal-moment Appell polynomials A_n from

       sum_{n>=0} A_n(x) t^n/n! = exp(x t) / M(t),

   where M is the moment generating function of the centered Rvachev law.

2. Verify, in exact rational arithmetic, the new Koopman eigenvalue law

       P A_n = 2^{-n} A_n,

   for the affine smoothing operator

       (P f)(x) = (1/2) int_{-1}^1 f((x+u)/2) du.

   The script also verifies the differential--dilation Stein lowering law,
   the Appell spectral expansion of polynomials, and the q-Pochhammer
   characteristic polynomial on finite-degree polynomial spaces.

3. Evaluate the exact scalar Stein kernel at dyadic endpoint points.  The
   identities used are

       F(2^{-n}) = 2^{-n(n+1)/2}
                   sum_{k=0}^{floor(n/2)} mu_{2k}/((2k)!(n-2k)!),

       tau(1-q) = ((1-q)F(q/2) + 2F(q/4))/F(q).

   All dyadic F-values and Stein-kernel values are exact rational numbers.
   High-precision floating point is used only for the Lambert-W comparison.

4. Simulate the stationary affine chain to check the exact forward/reverse
   Appell lag correlations and their asymmetric decay rates.

Outputs are written below the directory containing this script:

  data/appell_polynomials.tex
  data/gram_matrix.tex
  data/exact_verification.tex
  data/stein_kernel_table.csv
  data/lag_correlations.csv
  figures/stein_kernel_endpoint_ratio.pdf and .png
  figures/appell_lag_asymmetry.pdf and .png
  numerical_summary.txt

Dependencies: Python 3.10+, sympy, mpmath, numpy, matplotlib.
No network access is required.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import mpmath as mp
import numpy as np
import sympy as sp

# Matplotlib is imported only after selecting a non-interactive backend.
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


X, T, U = sp.symbols("x t u")


@dataclass(frozen=True)
class ExactData:
    """Container for exact cumulants, moments, and Appell polynomials."""

    cumulants: List[sp.Rational]
    moments: List[sp.Rational]
    appell: List[sp.Expr]


def centered_rvachev_cumulants(max_order: int) -> List[sp.Rational]:
    r"""Return cumulants kappa_0,...,kappa_max_order exactly.

    For the centered Rvachev random variable

        Y = sum_{j>=1} 2^{-j} U_j,   U_j ~ Unif[-1,1],

    the odd cumulants vanish and

        kappa_{2m} = 2^{2m-1} B_{2m}/(m(4^m-1)).

    SymPy's Bernoulli numbers use the convention B_2=1/6, B_4=-1/30.
    """

    if max_order < 0:
        raise ValueError("max_order must be nonnegative")
    kappa: List[sp.Rational] = [sp.Rational(0) for _ in range(max_order + 1)]
    for n in range(2, max_order + 1, 2):
        m = n // 2
        kappa[n] = sp.cancel(
            sp.Rational(2 ** (2 * m - 1), 1)
            * sp.bernoulli(2 * m)
            / (sp.Rational(m, 1) * (4**m - 1))
        )
    return kappa


def moments_from_cumulants(cumulants: Sequence[sp.Rational]) -> List[sp.Rational]:
    r"""Recover raw moments from cumulants by the standard triangular recurrence.

    With mu_0=1,

        mu_n = sum_{j=1}^n binom(n-1,j-1) kappa_j mu_{n-j}.

    The centered law is symmetric, so all odd moments obtained here are zero.
    """

    max_order = len(cumulants) - 1
    moments: List[sp.Rational] = [sp.Rational(0) for _ in range(max_order + 1)]
    moments[0] = sp.Rational(1)
    for n in range(1, max_order + 1):
        moments[n] = sp.cancel(
            sum(
                sp.binomial(n - 1, j - 1) * cumulants[j] * moments[n - j]
                for j in range(1, n + 1)
            )
        )
    return moments


def appell_polynomials(moments: Sequence[sp.Rational], max_degree: int) -> List[sp.Expr]:
    r"""Construct A_0,...,A_max_degree from exp(x t)/M(t)."""

    if len(moments) <= max_degree:
        raise ValueError("moments must be available through max_degree")
    mgf = sum(moments[n] * T**n / sp.factorial(n) for n in range(max_degree + 1))
    reciprocal = sp.series(1 / mgf, T, 0, max_degree + 1).removeO()
    generating = sp.series(sp.exp(X * T) * reciprocal, T, 0, max_degree + 1).removeO().expand()
    return [sp.expand(generating.coeff(T, n) * sp.factorial(n)) for n in range(max_degree + 1)]


def markov_apply(poly: sp.Expr, contraction: sp.Rational = sp.Rational(1, 2)) -> sp.Expr:
    r"""Apply the affine-uniform Markov operator exactly to a polynomial.

    For r in (0,1),

        P_r f(x) = (1/2) int_{-1}^1 f(r x + (1-r)u) du.

    The main Fabius/Rvachev case is r=1/2.
    """

    r = sp.Rational(contraction)
    transformed = poly.subs(X, r * X + (1 - r) * U)
    return sp.expand(sp.integrate(transformed, (U, -1, 1)) / 2)


def exact_expectation(poly: sp.Expr, moments: Sequence[sp.Rational]) -> sp.Rational:
    """Evaluate E[p(Y)] exactly from the moment table."""

    p = sp.Poly(sp.expand(poly), X)
    value = sp.Rational(0)
    for exponent, coefficient in p.terms():
        degree = exponent[0]
        if degree >= len(moments):
            raise ValueError("moment table too short for polynomial")
        value += coefficient * moments[degree]
    return sp.cancel(value)


def dyadic_fabius_value(n: int, moments: Sequence[sp.Rational]) -> sp.Rational:
    r"""Return the exact rational value F(2^{-n})."""

    if n < 1:
        raise ValueError("n must be positive")
    if n >= len(moments):
        raise ValueError("moment table must extend at least through n")
    finite_sum = sp.Rational(0)
    for k in range(n // 2 + 1):
        finite_sum += moments[2 * k] / (sp.factorial(2 * k) * sp.factorial(n - 2 * k))
    return sp.cancel(sp.Rational(1, 2) ** (n * (n + 1) // 2) * finite_sum)


def dyadic_stein_kernel(n: int, f_values: Dict[int, sp.Rational]) -> sp.Rational:
    r"""Return tau(1-2^{-n}) exactly from three dyadic F-values."""

    q = sp.Rational(1, 2**n)
    return sp.cancel(((1 - q) * f_values[n + 1] + 2 * f_values[n + 2]) / f_values[n])


def latex_expr(expr: sp.Expr) -> str:
    """Compact LaTeX rendering used in generated tables."""

    return sp.latex(sp.factor(expr), order="lex")


def write_appell_table(path: Path, appell: Sequence[sp.Expr], max_degree: int = 10) -> None:
    rows = [r"\begingroup", r"\scriptsize", r"\begin{longtable}{@{}c p{0.80\textwidth}@{}}", r"\toprule", r"$n$ & $\mathcal A_n(x)$ \\", r"\midrule", r"\endfirsthead", r"\toprule", r"$n$ & $\mathcal A_n(x)$ \\", r"\midrule", r"\endhead"]
    for n in range(max_degree + 1):
        rows.append(f"{n} & $ {latex_expr(appell[n])} $ " + r" \\")
    rows.extend([r"\bottomrule", r"\end{longtable}", r"\endgroup"])
    path.write_text("\n".join(rows) + "\n", encoding="utf-8")


def write_gram_table(
    path: Path,
    appell: Sequence[sp.Expr],
    moments: Sequence[sp.Rational],
    indices: Sequence[int] = (1, 2, 3, 4, 5, 6),
) -> Dict[Tuple[int, int], sp.Rational]:
    gram: Dict[Tuple[int, int], sp.Rational] = {}
    for m in indices:
        for n in indices:
            gram[(m, n)] = exact_expectation(appell[m] * appell[n], moments)

    header = " & ".join([r"$m\backslash n$"] + [f"${n}$" for n in indices]) + r" \\"
    rows = [r"\begin{center}", r"\scriptsize", r"\renewcommand{\arraystretch}{1.35}", r"\begin{tabular}{c" + "c" * len(indices) + "}", r"\toprule", header, r"\midrule"]
    for m in indices:
        entries = [f"${m}$"] + [f"$ {latex_expr(gram[(m,n)])} $" for n in indices]
        rows.append(" & ".join(entries) + r" \\")
    rows.extend([r"\bottomrule", r"\end{tabular}", r"\end{center}"])
    path.write_text("\n".join(rows) + "\n", encoding="utf-8")
    return gram


def symbolic_verifications(data: ExactData, max_degree: int = 10) -> Dict[str, object]:
    """Perform exact identities and return a machine-readable result dictionary."""

    appell = data.appell
    moments = data.moments

    eigen_residuals = [
        sp.simplify(markov_apply(appell[n]) - sp.Rational(1, 2**n) * appell[n])
        for n in range(max_degree + 1)
    ]

    # Differential--dilation Stein operator S=(I-P)D.
    stein_residuals = []
    for n in range(1, max_degree + 1):
        derivative = sp.diff(appell[n], X)
        s_value = sp.expand(derivative - markov_apply(derivative))
        target = sp.Rational(n) * (1 - sp.Rational(1, 2 ** (n - 1))) * appell[n - 1]
        stein_residuals.append(sp.simplify(s_value - target))

    # Spectral expansion of a deliberately nontrivial test polynomial.
    test_poly = 7 * X**10 - 3 * X**9 + 5 * X**6 - 11 * X**3 + 2 * X - 13
    spectral_reconstruction = sp.Rational(0)
    for n in range(0, 11):
        coefficient = exact_expectation(sp.diff(test_poly, X, n), moments) / sp.factorial(n)
        spectral_reconstruction += coefficient * appell[n]
    spectral_residual = sp.simplify(sp.expand(spectral_reconstruction - test_poly))

    # Characteristic polynomial of P on Pi_d in the monomial basis.
    z = sp.symbols("z")
    determinant_residuals = []
    for d in range(0, 9):
        matrix = sp.zeros(d + 1)
        basis = [X**j for j in range(d + 1)]
        for j, monomial in enumerate(basis):
            image = sp.Poly(markov_apply(monomial), X)
            for i in range(d + 1):
                matrix[i, j] = image.coeff_monomial(X**i)
        char_det = sp.factor((sp.eye(d + 1) - z * matrix).det())
        qpoch = sp.factor(sp.prod(1 - z * sp.Rational(1, 2**n) for n in range(d + 1)))
        determinant_residuals.append(sp.simplify(char_det - qpoch))

    all_zero = lambda items: all(sp.simplify(item) == 0 for item in items)
    return {
        "eigen_residuals": eigen_residuals,
        "stein_residuals": stein_residuals,
        "spectral_residual": spectral_residual,
        "determinant_residuals": determinant_residuals,
        "all_eigen_checks_pass": all_zero(eigen_residuals),
        "all_stein_checks_pass": all_zero(stein_residuals),
        "spectral_check_pass": spectral_residual == 0,
        "all_determinant_checks_pass": all_zero(determinant_residuals),
    }


def write_verification_table(path: Path, checks: Dict[str, object], max_degree: int) -> None:
    statuses = [
        (rf"$P\mathcal A_n=2^{{-n}}\mathcal A_n$ for $0\le n\le {max_degree}$", checks["all_eigen_checks_pass"]),
        (rf"$(I-P)D\mathcal A_n=n(1-2^{{1-n}})\mathcal A_{{n-1}}$ for $1\le n\le {max_degree}$", checks["all_stein_checks_pass"]),
        ("Appell spectral reconstruction of a degree-10 test polynomial", checks["spectral_check_pass"]),
        (r"$\det(I-zP|_{\Pi_d})=(z;1/2)_{d+1}$ for $0\le d\le8$", checks["all_determinant_checks_pass"]),
    ]
    rows = [r"\begin{center}", r"\begin{tabularx}{0.96\textwidth}{@{}Xc@{}}", r"\toprule", r"Exact symbolic identity & Result \\", r"\midrule"]
    for description, passed in statuses:
        result = r"\textbf{PASS}" if passed else r"\textbf{FAIL}"
        rows.append(f"{description} & {result} " + r" \\")
    rows.extend([r"\bottomrule", r"\end{tabularx}", r"\end{center}"])
    path.write_text("\n".join(rows) + "\n", encoding="utf-8")


def rational_to_decimal(value: sp.Rational, digits: int = 60) -> mp.mpf:
    """Convert an exact SymPy rational to mpmath without binary-float loss."""

    return mp.mpf(str(sp.N(value, digits)))


def endpoint_experiment(
    data_dir: Path,
    figures_dir: Path,
    moments: Sequence[sp.Rational],
    max_n: int = 120,
) -> Tuple[Dict[int, sp.Rational], Dict[int, sp.Rational], List[Dict[str, str]]]:
    """Compute exact dyadic Stein kernels and the Lambert-W comparison table."""

    f_values = {n: dyadic_fabius_value(n, moments) for n in range(1, max_n + 3)}
    tau_values = {n: dyadic_stein_kernel(n, f_values) for n in range(1, max_n + 1)}

    mp.mp.dps = 100
    log2 = mp.log(2)
    selected = [2, 3, 4, 5, 8, 10, 15, 20, 30, 40, 60, 80, 100, 120]
    rows: List[Dict[str, str]] = []
    for n in selected:
        q = mp.power(2, -n)
        lam = -mp.lambertw(-log2 * q, -1) / log2
        tau = rational_to_decimal(tau_values[n], 110)
        fval = rational_to_decimal(f_values[n], 110)
        rho = mp.sqrt(2 * mp.log(1 / fval) / log2)
        elasticity_exact = rational_to_decimal(sp.Rational(2 ** (n - 1)) * f_values[n] / f_values[n - 1], 110)
        first_ratio = tau * lam / q
        rho_ratio = tau * rho / q
        local_watson = (tau / q) - (elasticity_exact - elasticity_exact**2)
        rows.append(
            {
                "n": str(n),
                "q=2^-n": mp.nstr(q, 22),
                "F(q)_exact": str(f_values[n]),
                "tau(1-q)_exact": str(tau_values[n]),
                "lambda(q)": mp.nstr(lam, 22),
                "rho(F(q))": mp.nstr(rho, 22),
                "tau*lambda/q": mp.nstr(first_ratio, 22),
                "tau*rho/q": mp.nstr(rho_ratio, 22),
                "elasticity": mp.nstr(elasticity_exact, 22),
                "tau/q-(E-E^2)": mp.nstr(local_watson, 22),
            }
        )

    csv_path = data_dir / "stein_kernel_table.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    # Dense curve for the endpoint plot; values remain exact until conversion.
    ns = np.arange(2, max_n + 1)
    ratios = []
    ratios_rho = []
    for n in ns:
        q = mp.power(2, -int(n))
        lam = -mp.lambertw(-log2 * q, -1) / log2
        tau = rational_to_decimal(tau_values[int(n)], 100)
        fval = rational_to_decimal(f_values[int(n)], 100)
        rho = mp.sqrt(2 * mp.log(1 / fval) / log2)
        ratios.append(float(tau * lam / q))
        ratios_rho.append(float(tau * rho / q))

    fig, ax = plt.subplots(figsize=(7.2, 4.5))
    ax.plot(ns, ratios, label=r"$\tau(1-2^{-n})\,\lambda(2^{-n})/2^{-n}$")
    ax.plot(ns, ratios_rho, label=r"$\tau(1-2^{-n})\,\rho(F(2^{-n}))/2^{-n}$")
    ax.axhline(1.0, linewidth=1.0, linestyle="--", label="predicted limit 1")
    ax.set_xlabel(r"dyadic depth $n$")
    ax.set_ylabel("normalized endpoint ratio")
    ax.set_title("Endpoint Stein-kernel normalization")
    ax.grid(True, alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(figures_dir / "stein_kernel_endpoint_ratio.pdf", bbox_inches="tight")
    fig.savefig(figures_dir / "stein_kernel_endpoint_ratio.png", dpi=220, bbox_inches="tight")
    plt.close(fig)

    return f_values, tau_values, rows


def numpy_polynomial_evaluator(poly: sp.Expr):
    """Create a NumPy-vectorized evaluator for a univariate SymPy polynomial."""

    return sp.lambdify(X, poly, modules="numpy")


def lag_correlation_experiment(
    data_dir: Path,
    figures_dir: Path,
    appell: Sequence[sp.Expr],
    moments: Sequence[sp.Rational],
    sample_size: int,
    max_lag: int = 8,
    seed: int = 20260830,
) -> List[Dict[str, str]]:
    """Compare exact and Monte Carlo forward/reverse A_2--A_4 correlations."""

    g24 = exact_expectation(appell[2] * appell[4], moments)
    a2 = numpy_polynomial_evaluator(appell[2])
    a4 = numpy_polynomial_evaluator(appell[4])

    rng = np.random.default_rng(seed)

    # Directly sample a stationary X_0 from 36 dyadic uniform digits.  The
    # omitted tail is bounded by 2^{-36}, far below Monte Carlo uncertainty.
    x0 = np.zeros(sample_size, dtype=np.float64)
    for j in range(1, 37):
        x0 += np.ldexp(rng.uniform(-1.0, 1.0, size=sample_size), -j)

    xk = x0.copy()
    a2_x0 = a2(x0)
    a4_x0 = a4(x0)
    rows: List[Dict[str, str]] = []
    exact_forward_values: List[float] = []
    exact_reverse_values: List[float] = []
    mc_forward_values: List[float] = []
    mc_reverse_values: List[float] = []
    lags = list(range(max_lag + 1))

    g24_float = float(g24)
    for lag in lags:
        if lag > 0:
            xk = (xk + rng.uniform(-1.0, 1.0, size=sample_size)) / 2.0
        mc_forward = float(np.mean(a2_x0 * a4(xk)))
        mc_reverse = float(np.mean(a4_x0 * a2(xk)))
        exact_forward = g24_float * 2.0 ** (-4 * lag)
        exact_reverse = g24_float * 2.0 ** (-2 * lag)
        exact_forward_values.append(exact_forward)
        exact_reverse_values.append(exact_reverse)
        mc_forward_values.append(mc_forward)
        mc_reverse_values.append(mc_reverse)
        rows.append(
            {
                "lag": str(lag),
                "exact_E[A2(X0)A4(Xk)]": f"{exact_forward:.18e}",
                "mc_E[A2(X0)A4(Xk)]": f"{mc_forward:.18e}",
                "exact_E[A4(X0)A2(Xk)]": f"{exact_reverse:.18e}",
                "mc_E[A4(X0)A2(Xk)]": f"{mc_reverse:.18e}",
            }
        )

    csv_path = data_dir / "lag_correlations.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    fig, ax = plt.subplots(figsize=(7.2, 4.7))
    ax.plot(lags, np.abs(exact_forward_values), marker="o", label=r"exact $|E[A_2(X_0)A_4(X_k)]|$")
    ax.plot(lags, np.abs(exact_reverse_values), marker="s", label=r"exact $|E[A_4(X_0)A_2(X_k)]|$")
    # At long lags the exact correlations fall below the Monte Carlo noise floor.
    # Show empirical markers only at lags 0 and 1, where they are resolvable; the
    # full empirical table is still written to CSV for reproducibility.
    visible_mc_lags = [0, 1]
    ax.scatter(visible_mc_lags, np.abs(mc_forward_values[:2]), marker="x", label="Monte Carlo forward (k=0,1)")
    ax.scatter(visible_mc_lags, np.abs(mc_reverse_values[:2]), marker="+", label="Monte Carlo reverse (k=0,1)")
    ax.set_yscale("log")
    ax.set_xlabel("lag k")
    ax.set_ylabel("absolute mixed Appell correlation")
    ax.set_title("Exact time asymmetry of the stationary affine chain")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(figures_dir / "appell_lag_asymmetry.pdf", bbox_inches="tight")
    fig.savefig(figures_dir / "appell_lag_asymmetry.png", dpi=220, bbox_inches="tight")
    plt.close(fig)

    return rows


def write_summary(
    path: Path,
    data: ExactData,
    checks: Dict[str, object],
    f_values: Dict[int, sp.Rational],
    tau_values: Dict[int, sp.Rational],
    endpoint_rows: Sequence[Dict[str, str]],
    lag_rows: Sequence[Dict[str, str]],
    sample_size: int,
) -> None:
    g24 = exact_expectation(data.appell[2] * data.appell[4], data.moments)
    lines = [
        "DYADIC STEIN--KOOPMAN EXPERIMENT SUMMARY",
        "=========================================",
        "",
        "All symbolic calculations use exact SymPy rational arithmetic.",
        "Floating-point arithmetic is used only for Lambert-W evaluation and Monte Carlo checks.",
        "",
        f"Koopman eigenchecks through degree 10: {checks['all_eigen_checks_pass']}",
        f"Differential--dilation Stein checks through degree 10: {checks['all_stein_checks_pass']}",
        f"Degree-10 Appell spectral reconstruction: {checks['spectral_check_pass']}",
        f"q-Pochhammer determinant checks through degree 8: {checks['all_determinant_checks_pass']}",
        "",
        f"Exact Gram entry E[A_2(Y) A_4(Y)] = {g24}",
        f"Exact lag-1 forward value = {sp.cancel(g24/16)}",
        f"Exact lag-1 reverse value = {sp.cancel(g24/4)}",
        f"Exact lag-1 difference (forward - reverse) = {sp.cancel(g24/16-g24/4)}",
        "",
        "Selected exact dyadic Stein-kernel values:",
    ]
    for n in [2, 3, 4, 5, 10, 20]:
        lines.append(f"  n={n:3d}: F(2^-n)={f_values[n]}, tau(1-2^-n)={tau_values[n]}")
    lines.extend([
        "",
        "Selected endpoint normalization ratios tau*lambda/q:",
    ])
    for row in endpoint_rows:
        lines.append(f"  n={int(row['n']):3d}: {row['tau*lambda/q']}")
    lines.extend([
        "",
        f"Monte Carlo sample size for lag experiment: {sample_size}",
        "Lag table:",
    ])
    for row in lag_rows:
        lines.append(
            "  k={lag}: exact forward={ef}, MC forward={mf}, exact reverse={er}, MC reverse={mr}".format(
                lag=row["lag"],
                ef=row["exact_E[A2(X0)A4(Xk)]"],
                mf=row["mc_E[A2(X0)A4(Xk)]"],
                er=row["exact_E[A4(X0)A2(Xk)]"],
                mr=row["mc_E[A4(X0)A2(Xk)]"],
            )
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sample-size",
        type=int,
        default=400_000,
        help="Monte Carlo sample size for the lag-correlation check (default: 400000)",
    )
    parser.add_argument(
        "--max-dyadic-depth",
        type=int,
        default=120,
        help="largest n used in the exact endpoint table and figure (default: 120)",
    )
    args = parser.parse_args()
    if args.sample_size < 10_000:
        raise ValueError("sample size must be at least 10000 for a meaningful check")
    if args.max_dyadic_depth < 20:
        raise ValueError("max dyadic depth must be at least 20")

    root = Path(__file__).resolve().parent
    data_dir = root / "data"
    figures_dir = root / "figures"
    data_dir.mkdir(parents=True, exist_ok=True)
    figures_dir.mkdir(parents=True, exist_ok=True)

    # Moments must extend beyond max_dyadic_depth for the exact finite sum.
    max_order = max(args.max_dyadic_depth + 4, 24)
    cumulants = centered_rvachev_cumulants(max_order)
    moments = moments_from_cumulants(cumulants)
    appell = appell_polynomials(moments, 12)
    data = ExactData(cumulants=cumulants, moments=moments, appell=appell)

    checks = symbolic_verifications(data, max_degree=10)
    if not all(
        bool(checks[key])
        for key in (
            "all_eigen_checks_pass",
            "all_stein_checks_pass",
            "spectral_check_pass",
            "all_determinant_checks_pass",
        )
    ):
        raise RuntimeError("at least one exact symbolic verification failed")

    write_appell_table(data_dir / "appell_polynomials.tex", appell, max_degree=10)
    write_gram_table(data_dir / "gram_matrix.tex", appell, moments)
    write_verification_table(data_dir / "exact_verification.tex", checks, max_degree=10)

    f_values, tau_values, endpoint_rows = endpoint_experiment(
        data_dir,
        figures_dir,
        moments,
        max_n=args.max_dyadic_depth,
    )
    lag_rows = lag_correlation_experiment(
        data_dir,
        figures_dir,
        appell,
        moments,
        sample_size=args.sample_size,
    )
    write_summary(
        root / "numerical_summary.txt",
        data,
        checks,
        f_values,
        tau_values,
        endpoint_rows,
        lag_rows,
        args.sample_size,
    )

    print("All exact symbolic checks passed.")
    print(f"Outputs written under: {root}")


if __name__ == "__main__":
    main()
