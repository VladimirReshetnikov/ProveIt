#!/usr/bin/env python3
"""High-precision experiments for dyadic-comb interpolation of the Fabius function.

This script accompanies the report
    Global Lagrange and Hermite Interpolation of the Fabius--Rvachev Functions
    on Dyadic Combs.

It has four goals.

1. Evaluate F(a/2^e) exactly as a rational number using the dyadic bit-split
   recurrence documented in the ProveIt Fabius-function corpus.
2. Evaluate the *mathematical* equispaced Lagrange polynomial by the second
   barycentric formula in sufficiently high precision.  Ordinary double
   precision is not reliable once the Lebesgue constant becomes enormous.
3. Construct the endpoint-jet family

       H_{N,r}(x) = S_r(x) + [x(1-x)]^{r+1} I^o_{N-2} g_r(x),
       g_r(x) = (F(x)-S_r(x))/[x(1-x)]^{r+1},

   where S_r is the symmetric beta-polynomial smoothstep and I^o interpolates
   on the N-1 interior nodes j/N.
4. Compare endpoint-jet clamping with full-grid confluent Hermite
   interpolation, which matches derivatives at every node.

All function samples and derivative data are exact rationals until the final
high-precision evaluation stage.  The default "report" run writes CSV tables
and publication-ready PDF figures.  The full report run is intentionally high precision and may take several
minutes; the ``--quick`` mode provides a fast reproducibility smoke test.

Usage
-----
    python fabius_dyadic_interpolation_experiments.py \
        --outdir results_and_figures

For a faster smoke test:
    python fabius_dyadic_interpolation_experiments.py \
        --outdir quick_results --quick

Dependencies: Python 3.10+, mpmath, matplotlib.
"""

from __future__ import annotations

import argparse
import csv
import math
import time
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp


# ---------------------------------------------------------------------------
# Exact Fabius values on dyadic rationals
# ---------------------------------------------------------------------------

@lru_cache(maxsize=None)
def inverse_power_values(max_exponent: int) -> Tuple[Fraction, ...]:
    """Return V_n = F(2^{-n}) for 0 <= n <= max_exponent.

    The recurrence is

      V_0 = 1,
      V_n = 1/((2^n-1) 2^{n(n-1)/2})
            * sum_{k=0}^{n-1} 2^{k(k-1)/2} V_k/(n-k+1)!.

    Every operation is exact in fractions.Fraction.
    """
    if max_exponent < 0:
        raise ValueError("max_exponent must be nonnegative")

    values: List[Fraction] = [Fraction(1)]
    for n in range(1, max_exponent + 1):
        total = Fraction(0)
        for k in range(n):
            total += (
                Fraction(2 ** (k * (k - 1) // 2), math.factorial(n - k + 1))
                * values[k]
            )
        denominator = (2**n - 1) * 2 ** (n * (n - 1) // 2)
        values.append(total / denominator)
    return tuple(values)


@lru_cache(maxsize=None)
def fixed_denominator_evaluator(exponent: int):
    """Return a memoized exact evaluator a -> F(a/2^exponent)."""
    if exponent < 0:
        raise ValueError("exponent must be nonnegative")
    values = inverse_power_values(exponent)
    denominator = 1 << exponent

    @lru_cache(maxsize=None)
    def evaluate(numerator: int) -> Fraction:
        if numerator <= 0:
            return Fraction(0)
        if numerator >= denominator:
            return Fraction(1)

        # Split at the leading binary digit: a = 2^b + q.
        b = numerator.bit_length() - 1
        r = exponent - b
        q = numerator - (1 << b)
        y = Fraction(q, denominator)

        # Exact Taylor block around 2^{-r}.
        taylor = Fraction(0)
        for j in range(r + 1):
            taylor += (
                Fraction(2 ** (j * (j + 1) // 2), math.factorial(j))
                * values[r - j]
                * y**j
            )
        return taylor - evaluate(q)

    return evaluate


def reduce_dyadic(numerator: int, exponent: int) -> Tuple[int, int]:
    """Cancel powers of two from numerator/2^exponent."""
    while exponent > 0 and numerator % 2 == 0:
        numerator //= 2
        exponent -= 1
    return numerator, exponent


def exact_fabius(numerator: int, exponent: int) -> Fraction:
    """Exact F(numerator/2^exponent), with 0 <= numerator <= 2^exponent."""
    numerator, exponent = reduce_dyadic(numerator, exponent)
    return fixed_denominator_evaluator(exponent)(numerator)


@lru_cache(maxsize=None)
def exact_fabius_derivative(order: int, numerator: int, exponent: int) -> Fraction:
    """Exact derivative F^(order)(numerator/2^exponent).

    The recursion uses

      F^(k)(x) = 2^k F^(k-1)(2x),                 0 <= x <= 1/2,
      F^(k)(x) = 2^k (-1)^(k-1) F^(k-1)(2-2x), 1/2 <= x <= 1.

    Positive-order derivatives at 0 and 1 are zero.
    """
    if order < 0:
        raise ValueError("order must be nonnegative")
    numerator, exponent = reduce_dyadic(numerator, exponent)
    if order == 0:
        return exact_fabius(numerator, exponent)
    if exponent == 0:
        return Fraction(0)

    denominator = 1 << exponent
    if 2 * numerator <= denominator:
        return 2**order * exact_fabius_derivative(order - 1, numerator, exponent - 1)
    return (
        2**order
        * (-1) ** (order - 1)
        * exact_fabius_derivative(order - 1, denominator - numerator, exponent - 1)
    )


def mp_fraction(value: Fraction) -> mp.mpf:
    """Convert an exact fraction at the active mpmath precision."""
    return mp.mpf(value.numerator) / value.denominator


# ---------------------------------------------------------------------------
# Polynomial ingredients
# ---------------------------------------------------------------------------

def smoothstep(order: int, x: mp.mpf) -> mp.mpf:
    r"""The symmetric beta polynomial S_r(x) = I_x(r+1,r+1)."""
    coefficient = mp.mpf(math.factorial(2 * order + 1)) / math.factorial(order) ** 2
    total = mp.mpf("0")
    for k in range(order + 1):
        total += (
            (-1) ** k
            * math.comb(order, k)
            * x ** (order + k + 1)
            / (order + k + 1)
        )
    return coefficient * total


def scaled_equispaced_weights(count_minus_one: int) -> List[mp.mpf]:
    """Weights (-1)^j C(n,j), scaled by their largest magnitude."""
    raw = [mp.mpf((-1) ** j * math.comb(count_minus_one, j)) for j in range(count_minus_one + 1)]
    scale = max(abs(value) for value in raw)
    return [value / scale for value in raw]


def barycentric_value(
    x: mp.mpf,
    nodes: Sequence[mp.mpf],
    values: Sequence[mp.mpf],
    weights: Sequence[mp.mpf],
) -> mp.mpf:
    """Second barycentric formula, with exact-node handling."""
    for node, value in zip(nodes, values):
        if x == node:
            return value
    terms = [weight / (x - node) for node, weight in zip(nodes, weights)]
    denominator = mp.fsum(terms)
    return mp.fsum(term * value for term, value in zip(terms, values)) / denominator


@dataclass
class StandardResult:
    N: int
    max_error: mp.mpf
    x_at_max_error: mp.mpf
    min_value: mp.mpf
    max_value: mp.mpf
    lebesgue_constant: mp.mpf


@dataclass
class JetResult:
    N: int
    order: int
    degree: int
    max_error: mp.mpf
    x_at_max_error: mp.mpf
    weighted_lebesgue: mp.mpf


@dataclass
class HermiteResult:
    N: int
    derivative_order: int
    degree: int
    max_error: mp.mpf
    x_at_max_error: mp.mpf


def standard_lagrange_experiment(N: int, grid_exponent: int, dps: int) -> StandardResult:
    """Maximum error and Lebesgue constant for ordinary global interpolation."""
    if N <= 0 or N & (N - 1):
        raise ValueError("N must be a positive power of two")

    with mp.workdps(dps):
        exponent = int(math.log2(N))
        evaluator = fixed_denominator_evaluator(exponent)
        nodes = [mp.mpf(j) / N for j in range(N + 1)]
        values = [mp_fraction(evaluator(j)) for j in range(N + 1)]
        weights = scaled_equispaced_weights(N)

        reference = fixed_denominator_evaluator(grid_exponent)
        grid_size = 1 << grid_exponent
        max_error = mp.mpf("0")
        x_at_max = mp.mpf("0")
        half_min = mp.inf
        half_max = -mp.inf
        lebesgue = mp.mpf("0")

        # Symmetry P_N(1-x)=1-P_N(x) allows us to sample only [0,1/2].
        for a in range(grid_size // 2 + 1):
            x = mp.mpf(a) / grid_size
            f = mp_fraction(reference(a))
            node_number = a * N
            if node_number % grid_size == 0:
                index = node_number // grid_size
                p = values[index]
                local_lebesgue = mp.mpf(1)
            else:
                terms = [weight / (x - node) for node, weight in zip(nodes, weights)]
                denominator = mp.fsum(terms)
                p = mp.fsum(term * value for term, value in zip(terms, values)) / denominator
                local_lebesgue = mp.fsum(abs(term) for term in terms) / abs(denominator)

            error = abs(p - f)
            if error > max_error:
                max_error = error
                x_at_max = x
            half_min = min(half_min, p)
            half_max = max(half_max, p)
            lebesgue = max(lebesgue, local_lebesgue)

        full_min = min(half_min, 1 - half_max)
        full_max = max(half_max, 1 - half_min)
        return StandardResult(N, max_error, x_at_max, full_min, full_max, lebesgue)


def endpoint_jet_family_experiment(
    N: int,
    orders: Sequence[int],
    grid_exponent: int,
    dps: int,
) -> List[JetResult]:
    """Evaluate several endpoint-jet orders while sharing cardinal functions.

    The weighted Lebesgue function is the operator norm for perturbations of the
    original interior F-values when the endpoint jets are held fixed.
    """
    if N <= 2 or N & (N - 1):
        raise ValueError("N must be a power of two greater than 2")
    if any(order < 0 for order in orders):
        raise ValueError("orders must be nonnegative")

    orders = list(dict.fromkeys(orders))
    with mp.workdps(dps):
        exponent = int(math.log2(N))
        node_evaluator = fixed_denominator_evaluator(exponent)
        nodes = [mp.mpf(j) / N for j in range(1, N)]
        f_values = [mp_fraction(node_evaluator(j)) for j in range(1, N)]
        weights = scaled_equispaced_weights(N - 2)

        transformed: Dict[int, List[mp.mpf]] = {}
        inverse_node_factors: Dict[int, List[mp.mpf]] = {}
        for order in orders:
            data: List[mp.mpf] = []
            inverse_factors: List[mp.mpf] = []
            for x, f in zip(nodes, f_values):
                factor = (x * (1 - x)) ** (order + 1)
                data.append((f - smoothstep(order, x)) / factor)
                inverse_factors.append(1 / factor)
            transformed[order] = data
            inverse_node_factors[order] = inverse_factors

        reference = fixed_denominator_evaluator(grid_exponent)
        grid_size = 1 << grid_exponent
        max_error = {order: mp.mpf("0") for order in orders}
        x_at_max = {order: mp.mpf("0") for order in orders}
        max_weighted_lebesgue = {order: mp.mpf("0") for order in orders}

        for a in range(grid_size // 2 + 1):
            x = mp.mpf(a) / grid_size
            f = mp_fraction(reference(a))

            # Every interpolant is exact at every comb node, including endpoints.
            node_number = a * N
            if node_number % grid_size == 0:
                continue
            if x == 0:
                continue

            terms = [weight / (x - node) for node, weight in zip(nodes, weights)]
            denominator = mp.fsum(terms)
            cardinals = [term / denominator for term in terms]
            absolute_cardinals = [abs(value) for value in cardinals]

            for order in orders:
                q = mp.fsum(
                    cardinal * datum
                    for cardinal, datum in zip(cardinals, transformed[order])
                )
                factor = (x * (1 - x)) ** (order + 1)
                h = smoothstep(order, x) + factor * q
                error = abs(h - f)
                if error > max_error[order]:
                    max_error[order] = error
                    x_at_max[order] = x

                weighted = factor * mp.fsum(
                    cardinal * inverse_factor
                    for cardinal, inverse_factor in zip(
                        absolute_cardinals, inverse_node_factors[order]
                    )
                )
                max_weighted_lebesgue[order] = max(
                    max_weighted_lebesgue[order], weighted
                )

        return [
            JetResult(
                N=N,
                order=order,
                degree=N + 2 * order,
                max_error=max_error[order],
                x_at_max_error=x_at_max[order],
                weighted_lebesgue=max_weighted_lebesgue[order],
            )
            for order in orders
        ]


# ---------------------------------------------------------------------------
# Full-grid confluent Hermite interpolation
# ---------------------------------------------------------------------------

def confluent_newton_coefficients(N: int, derivative_order: int) -> Tuple[List[mp.mpf], List[mp.mpf]]:
    """Newton nodes and coefficients for full-grid Hermite interpolation.

    Each dyadic node j/N is repeated derivative_order+1 times.  Repeated-node
    divided differences are supplied by F^(k)(j/N)/k!.
    """
    exponent = int(math.log2(N))
    repeated_nodes: List[mp.mpf] = []
    repeated_derivatives: List[List[mp.mpf]] = []

    for j in range(N + 1):
        node = mp.mpf(j) / N
        derivatives = [
            mp_fraction(exact_fabius_derivative(k, j, exponent))
            for k in range(derivative_order + 1)
        ]
        for _ in range(derivative_order + 1):
            repeated_nodes.append(node)
            repeated_derivatives.append(derivatives)

    total = len(repeated_nodes)
    divided = [[mp.mpf("0")] * (total - i) for i in range(total)]
    for i in range(total):
        divided[i][0] = repeated_derivatives[i][0]

    for order in range(1, total):
        for i in range(total - order):
            if repeated_nodes[i + order] == repeated_nodes[i]:
                divided[i][order] = (
                    repeated_derivatives[i][order] / math.factorial(order)
                )
            else:
                divided[i][order] = (
                    divided[i + 1][order - 1] - divided[i][order - 1]
                ) / (repeated_nodes[i + order] - repeated_nodes[i])

    coefficients = [divided[0][order] for order in range(total)]
    return repeated_nodes, coefficients


def evaluate_newton(x: mp.mpf, nodes: Sequence[mp.mpf], coefficients: Sequence[mp.mpf]) -> mp.mpf:
    """Evaluate a Newton polynomial by nested multiplication."""
    value = coefficients[-1]
    for k in range(len(coefficients) - 2, -1, -1):
        value = coefficients[k] + (x - nodes[k]) * value
    return value


def full_grid_hermite_experiment(
    N: int,
    derivative_order: int,
    grid_exponent: int,
    dps: int,
) -> HermiteResult:
    """Maximum error for derivatives 0,...,derivative_order fixed at all nodes."""
    with mp.workdps(dps):
        nodes, coefficients = confluent_newton_coefficients(N, derivative_order)
        reference = fixed_denominator_evaluator(grid_exponent)
        grid_size = 1 << grid_exponent
        max_error = mp.mpf("0")
        x_at_max = mp.mpf("0")

        for a in range(grid_size // 2 + 1):
            x = mp.mpf(a) / grid_size
            p = evaluate_newton(x, nodes, coefficients)
            error = abs(p - mp_fraction(reference(a)))
            if error > max_error:
                max_error = error
                x_at_max = x

        degree = (derivative_order + 1) * (N + 1) - 1
        return HermiteResult(N, derivative_order, degree, max_error, x_at_max)


# ---------------------------------------------------------------------------
# Profiles and output helpers
# ---------------------------------------------------------------------------

def interpolation_profile(N: int, jet_order: int, grid_exponent: int, dps: int):
    """Return full-interval profiles of F, P_N, and H_{N,r}."""
    with mp.workdps(dps):
        exponent = int(math.log2(N))
        node_eval = fixed_denominator_evaluator(exponent)
        full_nodes = [mp.mpf(j) / N for j in range(N + 1)]
        full_values = [mp_fraction(node_eval(j)) for j in range(N + 1)]
        full_weights = scaled_equispaced_weights(N)

        interior_nodes = full_nodes[1:-1]
        interior_weights = scaled_equispaced_weights(N - 2)
        transformed = []
        for x, f in zip(interior_nodes, full_values[1:-1]):
            factor = (x * (1 - x)) ** (jet_order + 1)
            transformed.append((f - smoothstep(jet_order, x)) / factor)

        ref = fixed_denominator_evaluator(grid_exponent)
        M = 1 << grid_exponent
        left_x: List[float] = []
        left_f: List[float] = []
        left_p: List[float] = []
        left_h: List[float] = []
        for a in range(M // 2 + 1):
            x = mp.mpf(a) / M
            f = mp_fraction(ref(a))
            p = barycentric_value(x, full_nodes, full_values, full_weights)
            q = barycentric_value(x, interior_nodes, transformed, interior_weights)
            h = smoothstep(jet_order, x) + (x * (1 - x)) ** (jet_order + 1) * q
            left_x.append(float(x))
            left_f.append(float(f))
            left_p.append(float(p))
            left_h.append(float(h))

        # Mirror by exact symmetry.
        x_full = left_x + [1 - x for x in reversed(left_x[:-1])]
        f_full = left_f + [1 - y for y in reversed(left_f[:-1])]
        p_full = left_p + [1 - y for y in reversed(left_p[:-1])]
        h_full = left_h + [1 - y for y in reversed(left_h[:-1])]
        return x_full, f_full, p_full, h_full


def write_csv(path: Path, headers: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(headers)
        writer.writerows(rows)


def sci(value: mp.mpf, digits: int = 16) -> str:
    return mp.nstr(value, digits, min_fixed=0, max_fixed=0)


def save_current_figure(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    plt.tight_layout()
    plt.savefig(path, bbox_inches="tight")
    plt.close()


def run_report(outdir: Path, quick: bool = False) -> None:
    """Generate all tables and figures used in the report."""
    outdir.mkdir(parents=True, exist_ok=True)
    figures = outdir / "figures"
    results = outdir / "results"
    figures.mkdir(exist_ok=True)
    results.mkdir(exist_ok=True)

    start = time.time()

    standard_config = [
        (4, 70), (8, 80), (16, 90), (32, 100), (64, 140), (128, 210)
    ]
    standard_grid = 11 if quick else 13
    standard_results = [
        standard_lagrange_experiment(N, standard_grid, dps)
        for N, dps in standard_config
    ]
    write_csv(
        results / "standard_lagrange.csv",
        ["N", "degree", "max_error", "x_at_max_error", "min_interpolant", "max_interpolant", "lebesgue_constant"],
        [
            [r.N, r.N, sci(r.max_error, 20), sci(r.x_at_max_error, 16),
             sci(r.min_value, 20), sci(r.max_value, 20), sci(r.lebesgue_constant, 20)]
            for r in standard_results
        ],
    )

    if quick:
        scan_config = {
            16: (list(range(0, 7)), 10, 90),
            32: (list(range(0, 10)), 10, 100),
            64: (list(range(10, 17)), 10, 130),
            128: (list(range(20, 27)), 9, 180),
            256: ([39, 40, 41, 42], 9, 180),
        }
    else:
        scan_config = {
            16: (list(range(0, 9)), 12, 90),
            32: (list(range(0, 11)), 12, 100),
            64: ([0, 2, 4, 6, 8] + list(range(10, 18)), 12, 140),
            128: (list(range(20, 27)), 12, 210),
            256: ([39, 40, 41, 42], 11, 210),
        }

    jet_results: List[JetResult] = []
    for N, (orders, grid_exponent, dps) in scan_config.items():
        jet_results.extend(endpoint_jet_family_experiment(N, orders, grid_exponent, dps))

    write_csv(
        results / "endpoint_jet_scan.csv",
        ["N", "jet_order_r", "degree", "max_error", "x_at_max_error", "weighted_lebesgue_constant"],
        [
            [r.N, r.order, r.degree, sci(r.max_error, 20), sci(r.x_at_max_error, 16), sci(r.weighted_lebesgue, 20)]
            for r in jet_results
        ],
    )

    hermite_cases = [
        (4, 1, 80), (4, 2, 90), (4, 3, 100),
        (8, 1, 90), (8, 2, 100), (8, 3, 120),
        (16, 1, 120), (16, 2, 150),
        (32, 1, 180),
    ]
    hermite_grid = 10 if quick else 12
    hermite_results = [
        full_grid_hermite_experiment(N, q, hermite_grid, dps)
        for N, q, dps in hermite_cases
    ]
    write_csv(
        results / "full_grid_hermite.csv",
        ["N", "matched_derivative_order_q", "degree", "max_error", "x_at_max_error"],
        [
            [r.N, r.derivative_order, r.degree, sci(r.max_error, 20), sci(r.x_at_max_error, 16)]
            for r in hermite_results
        ],
    )

    # Best observed orders and the two-mechanism heuristic.
    best_rows = []
    for N in sorted({r.N for r in jet_results}):
        group = [r for r in jet_results if r.N == N]
        best_error = min(group, key=lambda row: row.max_error)
        best_stability = min(group, key=lambda row: row.weighted_lebesgue)
        prediction = N / (math.log2(N) - 1.5)
        best_rows.append([
            N,
            best_error.order,
            sci(best_error.max_error, 20),
            best_stability.order,
            sci(best_stability.weighted_lebesgue, 20),
            f"{prediction:.8f}",
        ])
    write_csv(
        results / "optimal_jet_orders.csv",
        ["N", "error_optimal_r", "minimum_sampled_error", "stability_optimal_r", "minimum_sampled_weighted_lebesgue", "heuristic_N_over_log2N_minus_3over2"],
        best_rows,
    )

    # ----- Figures: one independent plot per file. -----
    plt.figure(figsize=(6.4, 4.2))
    plt.semilogy([r.N for r in standard_results], [float(r.max_error) for r in standard_results], marker="o")
    plt.xlabel("number of dyadic subintervals N")
    plt.ylabel("sampled uniform error")
    plt.title("Global equispaced Lagrange error for the Fabius function")
    plt.grid(True, which="both", alpha=0.3)
    save_current_figure(figures / "standard_error_growth.pdf")

    plt.figure(figsize=(6.4, 4.2))
    plt.semilogy([r.N for r in standard_results], [float(r.lebesgue_constant) for r in standard_results], marker="o")
    plt.xlabel("number of dyadic subintervals N")
    plt.ylabel("sampled Lebesgue constant")
    plt.title("Exponential conditioning loss on the dyadic comb")
    plt.grid(True, which="both", alpha=0.3)
    save_current_figure(figures / "standard_lebesgue_growth.pdf")

    for N in [32, 64, 128, 256]:
        group = sorted((r for r in jet_results if r.N == N), key=lambda row: row.order)
        plt.figure(figsize=(6.4, 4.2))
        plt.semilogy([r.order for r in group], [float(r.max_error) for r in group], marker="o")
        plt.xlabel("endpoint jet order r")
        plt.ylabel("sampled uniform error")
        plt.title(f"Endpoint-jet error scan, N={N}")
        plt.grid(True, which="both", alpha=0.3)
        save_current_figure(figures / f"jet_error_scan_N{N}.pdf")

        plt.figure(figsize=(6.4, 4.2))
        plt.semilogy([r.order for r in group], [float(r.weighted_lebesgue) for r in group], marker="o")
        plt.xlabel("endpoint jet order r")
        plt.ylabel("weighted Lebesgue constant")
        plt.title(f"Endpoint-jet operator conditioning, N={N}")
        plt.grid(True, which="both", alpha=0.3)
        save_current_figure(figures / f"jet_weighted_lebesgue_N{N}.pdf")

    # Compare F, P_32 and the near-optimal endpoint-jet polynomial.
    profile_grid = 10 if quick else 11
    x, f, p, h = interpolation_profile(32, 8, profile_grid, 120)
    plt.figure(figsize=(6.4, 4.2))
    plt.plot(x, f, label="F")
    plt.plot(x, p, label="ordinary Lagrange, N=32")
    plt.plot(x, h, label="endpoint jets, N=32, r=8")
    plt.xlabel("x")
    plt.ylabel("value")
    plt.title("Runge oscillation and its finite-N postponement")
    plt.legend()
    plt.grid(True, alpha=0.3)
    save_current_figure(figures / "interpolants_N32.pdf")

    plt.figure(figsize=(6.4, 4.2))
    endpoint = [i for i, value in enumerate(x) if value <= 0.18]
    plt.semilogy([x[i] for i in endpoint], [max(abs(p[i] - f[i]), 1e-300) for i in endpoint], label="ordinary Lagrange")
    plt.semilogy([x[i] for i in endpoint], [max(abs(h[i] - f[i]), 1e-300) for i in endpoint], label="endpoint jets r=8")
    plt.xlabel("x")
    plt.ylabel("absolute error")
    plt.title("Left-endpoint error profile at N=32")
    plt.legend()
    plt.grid(True, which="both", alpha=0.3)
    save_current_figure(figures / "endpoint_error_profile_N32.pdf")

    # Full-grid Hermite: show first-derivative matching as N grows.
    first_derivative = sorted(
        (r for r in hermite_results if r.derivative_order == 1),
        key=lambda row: row.N,
    )
    plt.figure(figsize=(6.4, 4.2))
    plt.semilogy([r.N for r in first_derivative], [float(r.max_error) for r in first_derivative], marker="o")
    plt.xlabel("number of dyadic subintervals N")
    plt.ylabel("sampled uniform error")
    plt.title("Matching F and F' at every dyadic node")
    plt.grid(True, which="both", alpha=0.3)
    save_current_figure(figures / "full_grid_hermite_error.pdf")

    elapsed = time.time() - start
    (outdir / "RUN_METADATA.txt").write_text(
        "Fabius dyadic interpolation experiment run\n"
        f"quick_mode={quick}\n"
        f"elapsed_seconds={elapsed:.3f}\n"
        f"mpmath_version={mp.__version__}\n"
        f"standard_grid_exponent={standard_grid}\n"
        f"full_grid_hermite_grid_exponent={hermite_grid}\n",
        encoding="utf-8",
    )
    print(f"Wrote report data to {outdir} in {elapsed:.2f} seconds.")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--outdir",
        type=Path,
        default=Path("fabius_interpolation_output"),
        help="directory for results, figures, and metadata",
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help="use coarser validation grids for a fast smoke test",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    run_report(args.outdir, quick=args.quick)


if __name__ == "__main__":
    main()
