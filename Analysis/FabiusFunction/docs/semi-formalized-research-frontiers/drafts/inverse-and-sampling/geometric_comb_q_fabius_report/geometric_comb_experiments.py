#!/usr/bin/env python3
"""Numerical and exact-arithmetic experiments for geometric-comb interpolation.

This script accompanies the report

    Geometric-Comb Interpolation, Gaussian Pascal Transforms,
    and the Fabius--Rvachev Boundary Layer.

It deliberately separates two kinds of computation:

1. Exact rational arithmetic (`fractions.Fraction`) is used for the Fabius
   moment recurrence, F(2^{-j}), Lagrange evaluation at rational points, the
   extrapolation residue at zero, and several algebraic identity checks.
2. Floating-point *logarithmic* arithmetic is used only for the Lebesgue
   function, whose values grow like 2^{n(n-1)/2}.  Working with logarithms
   prevents overflow and avoids subtractive cancellation because the
   Lebesgue function is a sum of absolute cardinal values.

The program has no network dependency.  It writes reproducibility data to
`data/` and figures to `figures/` relative to its own directory.

Required third-party packages:
    numpy, matplotlib, mpmath

Python 3.10 or later is recommended.
"""

from __future__ import annotations

import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable, Sequence

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np


ROOT = Path(__file__).resolve().parent
DATA_DIR = ROOT / "data"
FIGURE_DIR = ROOT / "figures"
DATA_DIR.mkdir(exist_ok=True)
FIGURE_DIR.mkdir(exist_ok=True)


# ---------------------------------------------------------------------------
# Basic exact q-algebra
# ---------------------------------------------------------------------------


def q_binomial_integer(n: int, k: int, base: int) -> int:
    """Return the Gaussian coefficient [n choose k]_base as an integer.

    For the experiments we need base=2.  The Pascal recurrence is used rather
    than a quotient so that integrality is manifest and no cancellation is
    delegated to floating point.
    """

    if k < 0 or k > n:
        return 0
    row = [0] * (k + 1)
    row[0] = 1
    for nn in range(1, n + 1):
        upper = min(nn, k)
        for kk in range(upper, 0, -1):
            row[kk] = row[kk] + base ** (nn - kk) * row[kk - 1]
    return row[k]


def q_pochhammer_fraction(q: Fraction, n: int) -> Fraction:
    """Compute (q;q)_n exactly."""

    result = Fraction(1)
    power = q
    for _ in range(1, n + 1):
        result *= 1 - power
        power *= q
    return result


def newton_basis_value(x: Fraction, c: Fraction, q: Fraction, k: int) -> Fraction:
    """N_k(x;c,q) = product_{r=0}^{k-1} (x-c q^r), exactly."""

    result = Fraction(1)
    node = c
    for _ in range(k):
        result *= x - node
        node *= q
    return result


def verify_gaussian_pascal_basis(max_degree: int = 9) -> None:
    """Verify x^m = sum_k c^{m-k} [m choose k]_q N_k(x;c,q).

    The check uses q=1/2, c=3/2, x=7/5 and exact rational arithmetic.  It is
    not a proof, but it catches sign, exponent, and normalization errors in
    the implementation and in the formulas used by the later experiments.
    """

    q = Fraction(1, 2)
    c = Fraction(3, 2)
    x = Fraction(7, 5)
    for m in range(max_degree + 1):
        rhs = Fraction(0)
        # [m choose k]_{1/2} is obtained from reciprocity and the integer
        # Gaussian coefficient at base 2:
        # [m choose k]_{1/2} = 2^{-k(m-k)} [m choose k]_2.
        for k in range(m + 1):
            qbin = Fraction(q_binomial_integer(m, k, 2), 2 ** (k * (m - k)))
            rhs += c ** (m - k) * qbin * newton_basis_value(x, c, q, k)
        assert rhs == x**m, (m, rhs, x**m)


def complete_homogeneous(values: Sequence[Fraction], degree: int) -> Fraction:
    """Complete homogeneous symmetric polynomial h_degree(values).

    Dynamic programming multiplies the generating functions
    product_i (1-values[i] t)^{-1}, truncated at the requested degree.
    """

    coeffs = [Fraction(0)] * (degree + 1)
    coeffs[0] = Fraction(1)
    for value in values:
        for d in range(1, degree + 1):
            coeffs[d] += value * coeffs[d - 1]
    return coeffs[degree]


def verify_exact_residual(max_n: int = 7, max_r: int = 5) -> None:
    """Verify the monomial interpolation residual identity exactly.

    x^{n+1+r} - I_n(x^{n+1+r})
      = N_{n+1}(x) h_r(x,c,cq,...,cq^n).
    """

    q = Fraction(1, 2)
    c = Fraction(4, 3)
    x = Fraction(11, 13)
    for n in range(max_n + 1):
        nodes = [c * q**j for j in range(n + 1)]
        for r in range(max_r + 1):
            degree = n + 1 + r
            values = [node**degree for node in nodes]
            interpolated = lagrange_evaluate_exact(nodes, values, x)
            residual = x**degree - interpolated
            expected = newton_basis_value(x, c, q, n + 1) * complete_homogeneous(
                [x, *nodes], r
            )
            assert residual == expected, (n, r, residual, expected)


# ---------------------------------------------------------------------------
# Exact Fabius values on the inverse-dyadic comb
# ---------------------------------------------------------------------------


def fabius_moment_coefficients(max_n: int) -> list[Fraction]:
    r"""Return a_n = E[X^n]/n! for the standard Fabius law.

    The recurrence comes from

        A(2z) = ((e^z-1)/z) A(z),
        A(z)  = sum_{n>=0} a_n z^n,

    and is

        (2^n-1) a_n = sum_{j=0}^{n-1} a_j/(n-j+1)!.

    Every operation is rational.
    """

    a = [Fraction(1)]
    factorials = [math.factorial(k) for k in range(max_n + 2)]
    for n in range(1, max_n + 1):
        rhs = sum(
            (a[j] / factorials[n - j + 1] for j in range(n)),
            Fraction(0),
        )
        a.append(rhs / (2**n - 1))
    return a


def fabius_inverse_dyadic_values(a: Sequence[Fraction]) -> list[Fraction]:
    r"""Return F(2^{-j}) = 2^{-binom(j,2)} a_j exactly."""

    return [a[j] / 2 ** (j * (j - 1) // 2) for j in range(len(a))]


def lagrange_evaluate_exact(
    nodes: Sequence[Fraction], values: Sequence[Fraction], x: Fraction
) -> Fraction:
    """Evaluate a finite Lagrange interpolant using exact product cardinals."""

    if len(nodes) != len(values):
        raise ValueError("nodes and values must have the same length")
    for node, value in zip(nodes, values):
        if x == node:
            return value

    total = Fraction(0)
    for j, (node_j, value_j) in enumerate(zip(nodes, values)):
        numerator = Fraction(1)
        denominator = Fraction(1)
        for r, node_r in enumerate(nodes):
            if r == j:
                continue
            numerator *= x - node_r
            denominator *= node_j - node_r
        total += value_j * numerator / denominator
    return total


def geometric_nodes_half(n: int) -> list[Fraction]:
    """The inverse-dyadic nodes 1,1/2,...,2^{-n}."""

    return [Fraction(1, 2**j) for j in range(n + 1)]


def fabius_gap_and_boundary_data(max_n: int = 50) -> list[dict[str, float | int]]:
    """Compute two exact Fabius interpolation diagnostics.

    * Gap error at x=3/4.  This point lies in the persistent unsampled gap
      (1/2,1), and F(3/4)=1-F(1/4)=67/72 exactly.
    * Boundary residue I_n F(0).  The true value is zero, and the report proves
      a superexponential upper bound for this extrapolation error.
    """

    a = fabius_moment_coefficients(max_n)
    f_values = fabius_inverse_dyadic_values(a)
    x_gap = Fraction(3, 4)
    f_gap = Fraction(67, 72)
    rows: list[dict[str, float | int]] = []

    for n in range(1, max_n + 1):
        nodes = geometric_nodes_half(n)
        values = f_values[: n + 1]
        p_gap = lagrange_evaluate_exact(nodes, values, x_gap)
        gap_error = p_gap - f_gap
        p_zero = lagrange_evaluate_exact(nodes, values, Fraction(0))

        gap_log10 = (
            math.log10(abs(gap_error.numerator))
            - math.log10(gap_error.denominator)
            if gap_error
            else -math.inf
        )
        boundary_neg_log10 = (
            math.log10(p_zero.denominator) - math.log10(abs(p_zero.numerator))
            if p_zero
            else math.inf
        )
        rows.append(
            {
                "n": n,
                "gap_interpolant": float(p_gap),
                "gap_error_log10_abs": gap_log10,
                "gap_error_sign": 0 if not gap_error else (1 if gap_error > 0 else -1),
                "boundary_residue_neg_log10_abs": boundary_neg_log10,
                "boundary_residue_zero": int(p_zero == 0),
            }
        )
    return rows


def fabius_newton_coefficient(k: int, a: Sequence[Fraction]) -> Fraction:
    r"""Exact Newton coefficient for F on 1,1/2,...,2^{-k}.

    The report proves

      gamma_k = 1/(1/2;1/2)_k * sum_{j=0}^k (-1)^j [k choose j]_2 a_j.

    This formula exposes the base-2 Gaussian transform directly.
    """

    if k >= len(a):
        raise ValueError("moment table is too short")
    numerator = sum(
        (
            (-1 if j % 2 else 1)
            * q_binomial_integer(k, j, 2)
            * a[j]
            for j in range(k + 1)
        ),
        Fraction(0),
    )
    return numerator / q_pochhammer_fraction(Fraction(1, 2), k)


# ---------------------------------------------------------------------------
# Lebesgue function in logarithmic arithmetic
# ---------------------------------------------------------------------------


def logsumexp(values: Iterable[float]) -> float:
    """Stable logarithm of a sum of exponentials."""

    values = list(values)
    maximum = max(values)
    return maximum + math.log(sum(math.exp(value - maximum) for value in values))


@dataclass(frozen=True)
class GeometricLebesgueRow:
    """Precomputed data for nodes 1,q,...,q^n, with 0<q<1."""

    q: float
    n: int
    nodes: np.ndarray
    log_abs_barycentric_weights: np.ndarray

    @staticmethod
    def create(q: float, n: int) -> "GeometricLebesgueRow":
        if not (0.0 < q < 1.0):
            raise ValueError("this real stability experiment requires 0<q<1")
        nodes = np.array([q**j for j in range(n + 1)], dtype=float)

        # prefix[k] = log (q;q)_k = sum_{r=1}^k log(1-q^r)
        prefix = np.zeros(n + 1, dtype=float)
        for k in range(1, n + 1):
            prefix[k] = prefix[k - 1] + math.log1p(-(q**k))

        log_q = math.log(q)
        log_weights = np.empty(n + 1, dtype=float)
        for j in range(n + 1):
            exponent = j * (j + 1) / 2.0 - n * j
            log_weights[j] = (
                exponent * log_q - prefix[j] - prefix[n - j]
            )
        return GeometricLebesgueRow(q, n, nodes, log_weights)

    def log_lebesgue(self, x: float) -> float:
        r"""Return log Lambda_n(x).

        We evaluate

          Lambda_n(x) = |prod_r(x-q^r)|
                        sum_j |lambda_j|/|x-q^j|.

        This first-barycentric/product representation has no alternating
        cancellation and remains reliable when Lambda_n is astronomically
        large.
        """

        differences = np.abs(x - self.nodes)
        nearest = int(np.argmin(differences))
        if differences[nearest] <= 8.0 * np.finfo(float).eps * max(1.0, abs(x)):
            return 0.0  # At a node the Lebesgue function equals one.

        log_product = float(np.log(differences).sum())
        terms = self.log_abs_barycentric_weights - np.log(differences)
        return log_product + logsumexp(float(value) for value in terms)


def golden_section_maximum(
    function: Callable[[float], float], left: float, right: float, iterations: int = 90
) -> tuple[float, float]:
    """Maximize a unimodal function on a bracket by golden-section search."""

    golden = (math.sqrt(5.0) - 1.0) / 2.0
    c = right - golden * (right - left)
    d = left + golden * (right - left)
    fc = function(c)
    fd = function(d)
    for _ in range(iterations):
        if fc > fd:
            right, d, fd = d, c, fc
            c = right - golden * (right - left)
            fc = function(c)
        else:
            left, c, fc = c, d, fd
            d = left + golden * (right - left)
            fd = function(d)
    x = (left + right) / 2.0
    return x, function(x)


def maximize_top_gap_lebesgue(row: GeometricLebesgueRow) -> tuple[float, float]:
    """Find the maximum on the persistent top gap (q,1).

    A coarse scan is used only to obtain a safe local bracket.  The peak is
    then refined by golden-section search.  The theorem in the report proves
    that this top-gap maximum is the global maximum asymptotically and that
    n(1-x_max)->1.
    """

    q = row.q
    epsilon = 1e-12
    grid = np.linspace(q + epsilon, 1.0 - epsilon, 1201)
    logs = np.array([row.log_lebesgue(float(x)) for x in grid])
    index = int(np.argmax(logs))
    left_index = max(0, index - 2)
    right_index = min(len(grid) - 1, index + 2)
    return golden_section_maximum(
        row.log_lebesgue, float(grid[left_index]), float(grid[right_index])
    )


def endpoint_lebesgue(q: float, n: int) -> float:
    r"""Exact product Lambda_n(0)=(-q;q)_n/(q;q)_n in floating point."""

    value = 1.0
    power = q
    for _ in range(1, n + 1):
        value *= (1.0 + power) / (1.0 - power)
        power *= q
    return value


def lebesgue_data(q: float = 0.5, max_n: int = 32) -> list[dict[str, float | int]]:
    """Compute endpoint and top-gap Lebesgue diagnostics."""

    mp.mp.dps = 80
    q_mp = mp.mpf(str(q))
    endpoint_limit = mp.qp(-q_mp, q_mp) / mp.qp(q_mp, q_mp)
    asymptotic_prefactor = 2 * mp.qp(-q_mp, q_mp) / mp.e

    rows: list[dict[str, float | int]] = []
    for n in range(2, max_n + 1):
        row = GeometricLebesgueRow.create(q, n)
        x_max, log_lambda = maximize_top_gap_lebesgue(row)
        asymptotic_log = (
            math.log(float(asymptotic_prefactor))
            - math.log(n)
            - (n * (n - 1) / 2.0) * math.log(q)
        )
        rows.append(
            {
                "n": n,
                "endpoint_lebesgue": endpoint_lebesgue(q, n),
                "endpoint_limit": float(endpoint_limit),
                "x_max": x_max,
                "n_times_one_minus_x_max": n * (1.0 - x_max),
                "log10_lambda_max": log_lambda / math.log(10.0),
                "log10_asymptotic": asymptotic_log / math.log(10.0),
                "lambda_over_asymptotic": math.exp(log_lambda - asymptotic_log),
            }
        )
    return rows


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------


def write_csv(path: Path, rows: Sequence[dict[str, float | int]]) -> None:
    if not rows:
        raise ValueError("cannot write an empty table")
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def save_figure(path_stem: Path) -> None:
    """Save both vector PDF and raster PNG versions of the active figure."""

    plt.tight_layout()
    plt.savefig(path_stem.with_suffix(".pdf"), bbox_inches="tight")
    plt.savefig(path_stem.with_suffix(".png"), dpi=180, bbox_inches="tight")
    plt.close()


def make_figures(
    lebesgue_rows: Sequence[dict[str, float | int]],
    fabius_rows: Sequence[dict[str, float | int]],
) -> None:
    ns = np.array([int(row["n"]) for row in lebesgue_rows])
    log_max = np.array([float(row["log10_lambda_max"]) for row in lebesgue_rows])
    log_asym = np.array([float(row["log10_asymptotic"]) for row in lebesgue_rows])

    plt.figure(figsize=(7.1, 4.4))
    plt.plot(ns, log_max, marker="o", markersize=3, label="computed top-gap maximum")
    plt.plot(ns, log_asym, linestyle="--", label="proved asymptotic")
    plt.xlabel("interpolation degree n")
    plt.ylabel(r"$\log_{10}\Lambda_n$")
    plt.title(r"Lebesgue growth for the half-base comb $1,2^{-1},\ldots,2^{-n}$")
    plt.legend()
    plt.grid(True, alpha=0.25)
    save_figure(FIGURE_DIR / "lebesgue_growth")

    scaled_location = np.array(
        [float(row["n_times_one_minus_x_max"]) for row in lebesgue_rows]
    )
    plt.figure(figsize=(7.1, 4.2))
    plt.plot(ns, scaled_location, marker="o", markersize=3, label=r"$n(1-x_n^*)$")
    plt.axhline(1.0, linestyle="--", label="proved limit 1")
    plt.xlabel("interpolation degree n")
    plt.ylabel("scaled distance from the outer node")
    plt.title("Location of the geometric-comb Lebesgue peak")
    plt.legend()
    plt.grid(True, alpha=0.25)
    save_figure(FIGURE_DIR / "lebesgue_peak_location")

    fab_ns = np.array([int(row["n"]) for row in fabius_rows])
    gap_logs = np.array([float(row["gap_error_log10_abs"]) for row in fabius_rows])
    reference = 0.25 * fab_ns**2 * math.log10(2.0)
    plt.figure(figsize=(7.1, 4.4))
    plt.plot(fab_ns, gap_logs, marker="o", markersize=3, label=r"$\log_{10}|I_nF(3/4)-F(3/4)|$")
    plt.plot(fab_ns, reference, linestyle="--", label=r"leading scale $\frac{1}{4}n^2\log_{10}2$")
    plt.xlabel("interpolation degree n")
    plt.ylabel("decimal logarithm of absolute error")
    plt.title("Divergence of the Fabius interpolant in the persistent gap")
    plt.legend()
    plt.grid(True, alpha=0.25)
    save_figure(FIGURE_DIR / "fabius_gap_divergence")

    # n=1 has an exactly zero boundary residue, so omit it from a logarithmic
    # plot.  The theorem gives |R_n| <= C 2^{-floor(n^2/4)}.
    finite_rows = [
        row
        for row in fabius_rows
        if not int(row["boundary_residue_zero"])
        and math.isfinite(float(row["boundary_residue_neg_log10_abs"]))
    ]
    boundary_ns = np.array([int(row["n"]) for row in finite_rows])
    actual = np.array(
        [float(row["boundary_residue_neg_log10_abs"]) for row in finite_rows]
    )
    mp.mp.dps = 80
    q_half = mp.mpf("0.5")
    bound_constant = mp.e / mp.qp(q_half, q_half) ** 2
    guaranteed = np.array(
        [
            math.floor(n * n / 4) * math.log10(2.0)
            - math.log10(float(bound_constant))
            for n in boundary_ns
        ]
    )
    plt.figure(figsize=(7.1, 4.4))
    plt.plot(boundary_ns, actual, marker="o", markersize=3, label=r"$-\log_{10}|I_nF(0)|$")
    plt.plot(boundary_ns, guaranteed, linestyle="--", label="proved lower bound on digits")
    plt.xlabel("interpolation degree n")
    plt.ylabel("correct decimal digits at the accumulation point")
    plt.title("Superexponential recovery of the flat Fabius boundary value")
    plt.legend()
    plt.grid(True, alpha=0.25)
    save_figure(FIGURE_DIR / "fabius_boundary_residue")


def write_identity_report(max_n: int = 18) -> None:
    a = fabius_moment_coefficients(max_n)
    lines = [
        "Exact identity checks for geometric-comb interpolation",
        "=======================================================",
        "",
        "Gaussian Pascal basis change: passed through degree 9.",
        "Monomial residual identity: passed for 0<=n<=7 and 0<=r<=5.",
        "",
        "First exact Fabius Newton coefficients gamma_k",
        "(coefficient of N_k(x)=prod_{r<k}(x-2^{-r})):",
        "",
    ]
    for k in range(min(max_n, 12) + 1):
        gamma = fabius_newton_coefficient(k, a)
        lines.append(f"k={k:2d}: {gamma}")
    lines.extend(
        [
            "",
            "All checks use Fraction; no tolerance is involved.",
        ]
    )
    (DATA_DIR / "identity_checks.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    verify_gaussian_pascal_basis()
    verify_exact_residual()

    lebesgue_rows = lebesgue_data(q=0.5, max_n=32)
    fabius_rows = fabius_gap_and_boundary_data(max_n=50)

    write_csv(DATA_DIR / "lebesgue_data.csv", lebesgue_rows)
    write_csv(DATA_DIR / "fabius_interpolation_data.csv", fabius_rows)
    write_identity_report()
    make_figures(lebesgue_rows, fabius_rows)

    mp.mp.dps = 60
    q = mp.mpf("0.5")
    endpoint_limit = mp.qp(-q, q) / mp.qp(q, q)
    global_prefactor = 2 * mp.qp(-q, q) / mp.e
    print("All exact identity checks passed.")
    print(f"Endpoint Lebesgue limit: {mp.nstr(endpoint_limit, 30)}")
    print(f"Global asymptotic prefactor: {mp.nstr(global_prefactor, 30)}")
    print(f"Wrote data to {DATA_DIR}")
    print(f"Wrote figures to {FIGURE_DIR}")


if __name__ == "__main__":
    main()
