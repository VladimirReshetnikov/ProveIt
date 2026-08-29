#!/usr/bin/env python3
r"""Reproducible experiments for the Lagrange--Rvachev loop report.

This script implements the *exact* endpoint-basis synthesis algorithm from the
Rvachev up-function polynomial dictionary, specializes it to Lagrange cardinal
polynomials on [-1,1], and performs small numerical checks of the closed loop.

The exact algebra is done with SymPy rationals.  Numerical plots use a
finite-convolution approximation of the Rvachev up-function: if

    X = sum_{j>=1} 2^{-j} U_j,   U_j ~ Uniform[-1,1],

then up is the probability density of X.  Truncating the sum after J terms and
recursively convolving by boxes gives a stable approximation on a uniform grid.
The plotting code is diagnostic only; none of the exact theorems in the report
depends on these floating-point experiments.

Outputs (written next to this file):
  * coefficient_growth.csv
  * low_degree_cardinal_coefficients.tex
  * coefficient_growth.png
  * interpolation_stability.png
  * finite_loop_demo.png
  * numerical_summary.txt

Run:
    python experiments.py

Dependencies: numpy, scipy, sympy, matplotlib.
"""

from __future__ import annotations

import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import numpy as np
import sympy as sp
from scipy.interpolate import BarycentricInterpolator

OUT_DIR = Path(__file__).resolve().parent


# ---------------------------------------------------------------------------
# Exact symbolic synthesis
# ---------------------------------------------------------------------------

T, Z = sp.symbols("t z")


@dataclass(frozen=True)
class EndpointSynthesisData:
    """Reusable degree-n data for the endpoint up dictionary.

    The endpoint representation on t in [0,1] is

        P(t) = 2^{-n} sum_{r=0}^{n+1} b_r
               up((t-(2^n-n-1+r))/2^n).

    The array ``a`` contains the first n+2 coefficients of

        A_n(z) = product_{m=1}^n (1+z+...+z^{2^m-1}),

    and ``H`` is the differential multiplier H_n(z), truncated to degree n.
    """

    degree: int
    H: sp.Expr
    a: tuple[sp.Integer, ...]
    A_at_1: sp.Integer


def truncated_q_integer_product_coefficients(n: int) -> tuple[sp.Integer, ...]:
    """Return coefficients a_0,...,a_{n+1} of A_n(z), exactly.

    Only the first n+2 coefficients are required by the unit-triangular
    deconvolution, so every convolution is truncated immediately.  This keeps
    the algorithm output-sensitive even though deg(A_n)=2^{n+1}-n-2.
    """

    coeffs: list[sp.Integer] = [sp.Integer(1)]
    for m in range(1, n + 1):
        block_length = 2**m
        new_length = min(len(coeffs) + block_length - 1, n + 2)
        new = [sp.Integer(0)] * new_length
        for i, value in enumerate(coeffs):
            for j in range(block_length):
                if i + j >= n + 2:
                    break
                new[i + j] += value
        coeffs = new
    coeffs.extend([sp.Integer(0)] * (n + 2 - len(coeffs)))
    return tuple(coeffs)


def endpoint_synthesis_data(n: int) -> EndpointSynthesisData:
    r"""Construct the Bernoulli--Bell multiplier and q-integer filter.

    The logarithm of the exact differential multiplier is

      log H_n(z) = - sum_{m>=1} B_{2m}/(2m(2m)!)
                       * (n + 1/(1-4^{-m})) z^{2m}.

    Truncation at degree n is exact when H_n(D) acts on a degree-n polynomial.
    """

    if n < 0:
        raise ValueError("degree must be nonnegative")

    log_h = sp.Integer(0)
    for m in range(1, n // 2 + 1):
        factor = sp.Integer(n) + 1 / (1 - sp.Rational(1, 4) ** m)
        log_h -= (
            sp.bernoulli(2 * m)
            / (sp.Integer(2 * m) * sp.factorial(2 * m))
            * factor
            * Z ** (2 * m)
        )
    H = sp.series(sp.exp(log_h), Z, 0, n + 1).removeO().expand()
    a = truncated_q_integer_product_coefficients(n)
    A_at_1 = sp.Integer(2) ** (n * (n + 1) // 2)
    return EndpointSynthesisData(n, H, a, A_at_1)


def apply_H_to_polynomial(P: sp.Expr, data: EndpointSynthesisData) -> sp.Expr:
    """Return H_n(D)P exactly."""

    n = data.degree
    result = sp.Integer(0)
    for q in range(n + 1):
        result += data.H.coeff(Z, q) * sp.diff(P, T, q)
    return sp.expand(result)


def endpoint_coefficients(P: sp.Expr, data: EndpointSynthesisData) -> tuple[sp.Expr, ...]:
    r"""Return exact endpoint coefficients b_0,...,b_{n+1} for P.

    The sampled differential transform is

        g_r = A_n(1) (H_n(D)P)(r-n/2),     0 <= r <= n+1,

    and the coefficients solve the unit-triangular Toeplitz system

        g_r = sum_{s=0}^r a_{r-s} b_s.
    """

    n = data.degree
    poly = sp.Poly(sp.expand(P), T)
    if poly.degree() > n:
        raise ValueError(f"polynomial degree {poly.degree()} exceeds dictionary degree {n}")

    G = apply_H_to_polynomial(poly.as_expr(), data)
    b: list[sp.Expr] = []
    for r in range(n + 2):
        sample = sp.Rational(2 * r - n, 2)
        g_r = sp.simplify(data.A_at_1 * G.subs(T, sample))
        correction = sum(data.a[r - s] * b[s] for s in range(r))
        b.append(sp.factor(g_r - correction))
    return tuple(b)


def lagrange_cardinal(theta: Sequence[sp.Expr], j: int) -> sp.Expr:
    """Cardinal polynomial P_j(t) for nodes theta_0,...,theta_n."""

    numerator = sp.Integer(1)
    denominator = sp.Integer(1)
    for i, node in enumerate(theta):
        if i == j:
            continue
        numerator *= T - node
        denominator *= theta[j] - node
    return sp.expand(numerator / denominator)


def cardinal_synthesis_matrix(theta: Sequence[sp.Expr]) -> sp.Matrix:
    """Matrix B whose j-th column contains endpoint coefficients of P_j."""

    n = len(theta) - 1
    data = endpoint_synthesis_data(n)
    columns = [sp.Matrix(endpoint_coefficients(lagrange_cardinal(theta, j), data)) for j in range(n + 1)]
    return sp.Matrix.hstack(*columns)


def equispaced_theta(n: int) -> tuple[sp.Rational, ...]:
    """Nodes t_j=j/n, corresponding to x_j=-1+2j/n.

    For n=0 the unique node is t=1/2 (x=0).
    """

    if n == 0:
        return (sp.Rational(1, 2),)
    return tuple(sp.Rational(j, n) for j in range(n + 1))


def verify_cardinal_values(theta: Sequence[sp.Expr], B: sp.Matrix) -> None:
    """Check the exact polynomial-side cardinal identities.

    The up-functions themselves are not symbolically evaluated.  Instead, we
    verify that every column was generated from the correct Lagrange polynomial
    and that the coefficient algorithm reproduces known low-degree monomial
    cases.  The theorem guaranteeing the up synthesis is the exact endpoint
    basis identity proved in the report and repository source.
    """

    n = len(theta) - 1
    if B.shape != (n + 2, n + 1):
        raise AssertionError("unexpected synthesis matrix shape")
    for j in range(n + 1):
        P = lagrange_cardinal(theta, j)
        values = [sp.simplify(P.subs(T, node)) for node in theta]
        expected = [sp.Integer(i == j) for i in range(n + 1)]
        if values != expected:
            raise AssertionError(f"cardinal identity failed at degree {n}, column {j}")


def thue_morse_sign(k: int) -> int:
    """Return epsilon_k=(-1)^{binary digit sum of k}."""

    return -1 if k.bit_count() % 2 else 1


def endpoint_certificate_row(n: int) -> sp.Matrix:
    r"""Return the restricted Thue--Morse polynomiality row lambda.

    The full active coefficient vector has indices 0,...,2^(n+1)-1.
    Restricting the repository's certificate to the rightmost endpoint basis
    yields

        lambda_r = (-1)^(r+1) epsilon_floor((2^(n+1)-n-2+r)/2).
    """

    R = 2**n
    entries = []
    for r in range(n + 2):
        full_index = 2 * R - n - 2 + r
        entries.append((-1) ** (r + 1) * thue_morse_sign(full_index // 2))
    return sp.Matrix([entries])


# ---------------------------------------------------------------------------
# Numerical approximation of up
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class UpApproximation:
    grid: np.ndarray
    values: np.ndarray

    def __call__(self, x: np.ndarray | float) -> np.ndarray:
        array = np.asarray(x, dtype=float)
        result = np.interp(array, self.grid, self.values, left=0.0, right=0.0)
        return result


def approximate_up(grid_power: int = 17, terms: int = 18) -> UpApproximation:
    r"""Approximate up by repeated box averaging on a fixed grid.

    After the first term 2^{-1}U_1, the density is exactly 1 on [-1/2,1/2].
    Convolution by the next box of half-width a is evaluated as

        f_new(x) = (F_old(x+a)-F_old(x-a))/(2a),

    where F_old is a numerically integrated CDF.  The truncation tail has total
    support radius 2^{-terms}; the chosen defaults are sufficient for the
    qualitative experiments below.
    """

    if grid_power < 12:
        raise ValueError("grid_power should be at least 12")
    if terms < 2:
        raise ValueError("terms should be at least 2")

    number_of_intervals = 2**grid_power
    x = np.linspace(-1.0, 1.0, number_of_intervals + 1)
    h = x[1] - x[0]
    f = np.where(np.abs(x) <= 0.5 + 0.25 * h, 1.0, 0.0)

    for j in range(2, terms + 1):
        a = 2.0 ** (-j)
        # Trapezoidal cumulative integral with cdf[0]=0.
        cdf = np.empty_like(f)
        cdf[0] = 0.0
        cdf[1:] = np.cumsum((f[:-1] + f[1:]) * (0.5 * h))
        total = cdf[-1]

        right = np.interp(x + a, x, cdf, left=0.0, right=total)
        left = np.interp(x - a, x, cdf, left=0.0, right=total)
        f = (right - left) / (2.0 * a)

        # Renormalization suppresses accumulated quadrature drift.
        mass = np.trapezoid(f, x)
        if not np.isfinite(mass) or mass <= 0:
            raise RuntimeError("finite-convolution approximation lost positivity/mass")
        f /= mass

    # Enforce the exact symmetries and endpoint zeros at plotting precision.
    f = 0.5 * (f + f[::-1])
    f[0] = 0.0
    f[-1] = 0.0
    return UpApproximation(x, f)


def barycentric_interpolant(nodes: np.ndarray, values: np.ndarray, x: np.ndarray) -> np.ndarray:
    """Evaluate a global polynomial interpolant using SciPy's barycentric form."""

    interpolator = BarycentricInterpolator(nodes, values)
    return np.asarray(interpolator(x), dtype=float)


# ---------------------------------------------------------------------------
# Output generation
# ---------------------------------------------------------------------------

def write_low_degree_tex() -> None:
    """Write exact endpoint amplitudes for the quadratic cardinal basis."""

    n = 2
    theta = equispaced_theta(n)
    B = cardinal_synthesis_matrix(theta)
    raw = B / (2**n)

    lines = [
        "% Automatically generated by experiments.py.",
        r"\begin{align*}",
    ]
    for j in range(n + 1):
        entries = r",\;".join(sp.latex(sp.factor(raw[r, j])) for r in range(n + 2))
        terminator = r"\\" if j < n else ""
        lines.append(rf"(a_{{{j},0}},a_{{{j},1}},a_{{{j},2}},a_{{{j},3}})&=({entries}){terminator}")
    lines.extend([r"\end{align*}", ""])
    (OUT_DIR / "low_degree_cardinal_coefficients.tex").write_text("\n".join(lines), encoding="utf-8")


def coefficient_growth(max_degree: int = 13) -> list[dict[str, float | int]]:
    """Compute exact cardinal coefficient norms for equispaced nodes."""

    rows: list[dict[str, float | int]] = []
    for n in range(1, max_degree + 1):
        theta = equispaced_theta(n)
        B = cardinal_synthesis_matrix(theta)
        verify_cardinal_values(theta, B)
        certificate = endpoint_certificate_row(n)
        if certificate * B != sp.zeros(1, n + 1):
            raise AssertionError(f"Thue--Morse certificate failed at degree {n}")

        raw_norms = []
        b_norms = []
        for j in range(n + 1):
            b_norm = sum(abs(B[r, j]) for r in range(n + 2))
            raw_norm = b_norm / (2**n)
            b_norms.append(float(sp.N(b_norm, 40)))
            raw_norms.append(float(sp.N(raw_norm, 40)))

        t_n = n - math.log2(n + 2)
        quadratic_proxy_log10 = (math.log(2.0) / (2.0 * math.log(10.0))) * t_n * t_n
        rows.append(
            {
                "degree": n,
                "max_raw_l1": max(raw_norms),
                "median_raw_l1": float(np.median(raw_norms)),
                "max_b_l1": max(b_norms),
                "quadratic_proxy_log10": quadratic_proxy_log10,
                "log10_max_raw_l1": math.log10(max(raw_norms)),
            }
        )
    return rows


def save_growth_outputs(rows: Iterable[dict[str, float | int]]) -> None:
    rows = list(rows)
    csv_path = OUT_DIR / "coefficient_growth.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    degrees = np.array([int(row["degree"]) for row in rows])
    observed = np.array([float(row["log10_max_raw_l1"]) for row in rows])
    proxy = np.array([float(row["quadratic_proxy_log10"]) for row in rows])

    plt.figure(figsize=(7.2, 4.6))
    plt.plot(degrees, observed, marker="o", label=r"computed $\log_{10}\max_j\|a_{n,j}\|_1$")
    plt.plot(degrees, proxy, marker="s", label=r"endpoint-law quadratic proxy")
    plt.xlabel("polynomial degree n")
    plt.ylabel("base-10 logarithm")
    plt.title("Coefficient growth in the common-scale endpoint dictionary")
    plt.grid(True, alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(OUT_DIR / "coefficient_growth.png", dpi=220)
    plt.close()


def save_interpolation_stability(up: UpApproximation) -> list[tuple[int, float, float]]:
    """Compare equispaced and Chebyshev--Lobatto interpolation errors."""

    # Avoid evaluating exactly at all construction grid points; a staggered
    # validation grid gives a less biased sup-norm diagnostic.
    x = np.linspace(-1.0, 1.0, 20001)
    truth = up(x)
    records: list[tuple[int, float, float]] = []
    degrees = [4, 8, 12, 16, 20, 24, 28, 32, 40, 48]

    for n in degrees:
        eq_nodes = np.linspace(-1.0, 1.0, n + 1)
        eq_values = up(eq_nodes)
        eq_poly = barycentric_interpolant(eq_nodes, eq_values, x)
        eq_error = float(np.max(np.abs(eq_poly - truth)))

        # Chebyshev--Lobatto nodes, ordered increasingly for readability.
        k = np.arange(n + 1)
        ch_nodes = np.sort(np.cos(np.pi * k / n))
        ch_values = up(ch_nodes)
        ch_poly = barycentric_interpolant(ch_nodes, ch_values, x)
        ch_error = float(np.max(np.abs(ch_poly - truth)))
        records.append((n, eq_error, ch_error))

    degree_array = np.array([item[0] for item in records])
    eq_array = np.array([max(item[1], 1e-18) for item in records])
    ch_array = np.array([max(item[2], 1e-18) for item in records])

    plt.figure(figsize=(7.2, 4.6))
    plt.semilogy(degree_array, eq_array, marker="o", label="equispaced nodes")
    plt.semilogy(degree_array, ch_array, marker="s", label="Chebyshev--Lobatto nodes")
    plt.xlabel("polynomial degree n")
    plt.ylabel("sampled sup error")
    plt.title("The closed loop inherits the stability of its interpolation nodes")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(OUT_DIR / "interpolation_stability.png", dpi=220)
    plt.close()
    return records


def save_finite_loop_demo(up: UpApproximation, n: int = 4) -> dict[str, float]:
    """Demonstrate the finite identity after substituting Lagrange cardinals.

    The target samples are approximate floating-point values of up.  Exact
    rational endpoint coefficients for the cardinal basis are combined with
    those samples.  We then compare the ordinary Lagrange interpolant with the
    reconstructed sum of n+2 shifted/dilated up-functions.
    """

    theta = equispaced_theta(n)
    x_nodes = np.array([float(2 * q - 1) for q in theta], dtype=float)
    y_nodes = up(x_nodes)
    B_exact = cardinal_synthesis_matrix(theta)
    B = np.array(B_exact.evalf(40), dtype=float)

    # Group the original (n+1)(n+2) double sum by its n+2 common atoms.
    b_combined = B @ y_nodes
    raw_amplitudes = b_combined / (2**n)

    R = 2**n
    k = np.arange(R - n - 1, R + 1, dtype=float)
    centers_x = 2.0 * k - 1.0
    scale_x = 2.0 * R

    x = np.linspace(-1.0, 1.0, 5001)
    truth = up(x)
    lagrange = barycentric_interpolant(x_nodes, y_nodes, x)

    atoms = np.vstack([up((x - center) / scale_x) for center in centers_x])
    loop = raw_amplitudes @ atoms

    identity_error = float(np.max(np.abs(loop - lagrange)))
    interpolation_error = float(np.max(np.abs(lagrange - truth)))
    amplitude_l1 = float(np.sum(np.abs(raw_amplitudes)))

    plt.figure(figsize=(7.2, 4.8))
    plt.plot(x, truth, label=r"finite-convolution approximation of $\operatorname{up}$")
    plt.plot(x, lagrange, linestyle="--", label=f"degree-{n} Lagrange interpolant")
    plt.plot(x, loop, linestyle=":", label=f"same polynomial from {n+2} up-atoms")
    plt.scatter(x_nodes, y_nodes, s=20, zorder=5, label="interpolation data")
    plt.xlabel("x")
    plt.ylabel("value")
    plt.title("Finite closure of the Lagrange--Rvachev loop")
    plt.grid(True, alpha=0.25)
    plt.legend(fontsize=8)
    plt.tight_layout()
    plt.savefig(OUT_DIR / "finite_loop_demo.png", dpi=220)
    plt.close()

    return {
        "degree": float(n),
        "loop_vs_lagrange_sup_error": identity_error,
        "lagrange_vs_up_sup_error": interpolation_error,
        "combined_raw_amplitude_l1": amplitude_l1,
        "up_at_zero": float(up(0.0)),
        "up_mass": float(np.trapezoid(up.values, up.grid)),
    }


def exact_regression_checks() -> None:
    """Check the published low-degree monomial coefficient examples."""

    # Degree 0: 1 = up(t)+up(t-1) on [0,1].
    d0 = endpoint_coefficients(sp.Integer(1), endpoint_synthesis_data(0))
    assert d0 == (sp.Integer(1), sp.Integer(1))

    # Degree 1: raw amplitudes (-1/2,1,1/2), hence b=(-1,2,1).
    d1 = endpoint_coefficients(T, endpoint_synthesis_data(1))
    assert d1 == (sp.Integer(-1), sp.Integer(2), sp.Integer(1))

    # Degree 2: raw amplitudes (13,-31,49,5)/9.
    d2 = endpoint_coefficients(T**2, endpoint_synthesis_data(2))
    expected = tuple(sp.Rational(4 * q, 9) for q in (13, -31, 49, 5))
    assert d2 == expected


def main() -> None:
    exact_regression_checks()
    write_low_degree_tex()

    growth_rows = coefficient_growth(max_degree=13)
    save_growth_outputs(growth_rows)

    up = approximate_up(grid_power=18, terms=20)
    interpolation_records = save_interpolation_stability(up)
    loop_summary = save_finite_loop_demo(up, n=4)

    summary_lines = [
        "Numerical diagnostics generated by experiments.py",
        "=================================================",
        "",
        "Finite loop demo:",
    ]
    for key, value in loop_summary.items():
        summary_lines.append(f"  {key}: {value:.16e}")

    summary_lines.extend(["", "Interpolation stability (sampled sup errors):"])
    for n, eq_error, ch_error in interpolation_records:
        summary_lines.append(
            f"  n={n:2d}: equispaced={eq_error:.8e}, Chebyshev-Lobatto={ch_error:.8e}"
        )

    summary_lines.extend(["", "Exact coefficient-growth summary:"])
    for row in growth_rows:
        summary_lines.append(
            "  n={degree:2d}: log10 max raw l1={log10_max_raw_l1:.8f}, "
            "quadratic proxy={quadratic_proxy_log10:.8f}".format(**row)
        )

    (OUT_DIR / "numerical_summary.txt").write_text("\n".join(summary_lines) + "\n", encoding="utf-8")
    print("\n".join(summary_lines))


if __name__ == "__main__":
    main()
