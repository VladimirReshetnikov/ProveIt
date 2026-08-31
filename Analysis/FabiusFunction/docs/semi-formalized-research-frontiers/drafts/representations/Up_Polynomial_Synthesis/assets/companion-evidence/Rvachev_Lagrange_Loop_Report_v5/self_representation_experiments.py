#!/usr/bin/env python3
r"""Reproducible experiments for the Rvachev--Lagrange loop report.

The report proves the following exact fixed-radius identity.  Let ``up`` be
Rvachev's even probability density supported on [-1,1], let p be a polynomial
of degree at most n, put m=2**n and h=1/m, and define

    A p = M_up(D)^{-1} p
        = sum_r gamma_r p^(r) / r!,

where 1/M_up(z)=sum_r gamma_r z^r/r!.  Then, on [-1,1],

    p(x) = h * sum_{k=-2m+1}^{2m-1} (A p)(k h) up(x-k h).

For interpolation nodes x_0,...,x_n and Lagrange cardinals ell_j, this gives
an exact coefficient matrix

    D[k,j] = (A ell_j)(k h),
    Btilde[i,k] = h up(x_i-k h),

with Btilde @ D = I.  Btilde is nonnegative and row-stochastic; D is signed
and has every row sum equal to one.  Consequently P=D @ Btilde is an exact
oblique projector in coefficient space.

This program performs four independent checks/experiments:

1. Exact rational verification of Btilde D=I for equispaced degrees
   n=1,2,4,8.  For these powers of two, both interpolation nodes and shift
   centers are dyadic, so every up-value is evaluated exactly as a Fraction.
2. Floating-point verification and reduced-QR computation of ||P||_2 without
   ever forming the enormous N-by-N matrix P.  If D=Q_D R_D and
   Btilde^T=Q_B R_B are thin QR factorizations, the nonzero singular values
   of P are those of R_D R_B^T.
3. Decoder-sign diagnostics.  Since Btilde is a Markov matrix, overlapping
   rows force every row-unital right inverse to contain negative entries.
   The script records the maximum row total variation of the canonical D and
   the elementary two-row lower bound 2/||b_i-b_j||_1.
4. Polynomial interpolation of up at equispaced and Chebyshev--Lobatto nodes.
   The resulting up-shift representation has *exactly the same* error because
   it is merely a factorization of the interpolation projector.  The code
   therefore compares the familiar Runge behavior with stable Chebyshev
   convergence.

No network access is used.  Dependencies are Python 3.10+, NumPy, SymPy,
mpmath, and Matplotlib.  Run from the directory containing this file:

    python self_representation_experiments.py

Use ``--quick`` to omit the degree-12 matrices and the high-precision
n=64 equispaced scan.  Results are written under ``results/`` and figures
under ``figures/``.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp
from numpy.polynomial import Polynomial


ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results"
FIGURES = ROOT / "figures"
RESULTS.mkdir(exist_ok=True)
FIGURES.mkdir(exist_ok=True)

X = sp.Symbol("x")
Z = sp.Symbol("z")


# ---------------------------------------------------------------------------
# Exact Bernoulli--Appell deconvolution coefficients
# ---------------------------------------------------------------------------


def gamma_coefficients(max_degree: int) -> list[Fraction]:
    r"""Return exact gamma_0,...,gamma_max_degree.

    Rvachev's up-density has cumulants

        kappa_{2r} = B_{2r} / (2r (1-4^{-r})),     kappa_{2r+1}=0,

    and

        1/M_up(z) = exp(-sum_{r>=1} kappa_{2r} z^{2r}/(2r)!)
                  = sum_{s>=0} gamma_s z^s/s!.

    Only finitely many terms can act on a polynomial of bounded degree, so the
    SymPy series below is exact rather than an approximation.
    """

    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")

    logarithm = sp.Integer(0)
    for r in range(1, max_degree // 2 + 1):
        kappa = sp.bernoulli(2 * r) / (
            sp.Integer(2 * r) * (1 - sp.Rational(1, 4) ** r)
        )
        logarithm -= kappa * Z ** (2 * r) / sp.factorial(2 * r)

    reciprocal_mgf = sp.series(
        sp.exp(logarithm), Z, 0, max_degree + 1
    ).removeO().expand()

    answer: list[Fraction] = []
    for s in range(max_degree + 1):
        value = sp.factor(reciprocal_mgf.coeff(Z, s) * sp.factorial(s))
        answer.append(Fraction(int(sp.numer(value)), int(sp.denom(value))))
    return answer


# ---------------------------------------------------------------------------
# Tiny exact polynomial package (ascending coefficients)
# ---------------------------------------------------------------------------


def poly_add(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    result = [Fraction(0)] * max(len(a), len(b))
    for i, value in enumerate(a):
        result[i] += value
    for i, value in enumerate(b):
        result[i] += value
    return result


def poly_scale(a: Sequence[Fraction], scalar: Fraction) -> list[Fraction]:
    return [scalar * value for value in a]


def poly_multiply(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    result = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, left in enumerate(a):
        for j, right in enumerate(b):
            result[i + j] += left * right
    return result


def poly_derivative(a: Sequence[Fraction]) -> list[Fraction]:
    if len(a) <= 1:
        return [Fraction(0)]
    return [Fraction(i) * a[i] for i in range(1, len(a))]


def poly_evaluate(a: Sequence[Fraction], point: Fraction) -> Fraction:
    value = Fraction(0)
    for coefficient in reversed(a):
        value = value * point + coefficient
    return value


def lagrange_polynomial_exact(
    nodes: Sequence[Fraction], index: int
) -> list[Fraction]:
    """Return the exact cardinal ell_index in the monomial basis."""

    numerator = [Fraction(1)]
    denominator = Fraction(1)
    xj = nodes[index]
    for r, xr in enumerate(nodes):
        if r == index:
            continue
        numerator = poly_multiply(numerator, [-xr, Fraction(1)])
        denominator *= xj - xr
    return [coefficient / denominator for coefficient in numerator]


def appell_evaluate_exact(
    polynomial: Sequence[Fraction],
    point: Fraction,
    gamma: Sequence[Fraction],
) -> Fraction:
    r"""Evaluate A p(point)=sum gamma_r p^(r)(point)/r! exactly."""

    total = Fraction(0)
    derivative = list(polynomial)
    for r, coefficient in enumerate(gamma):
        if r >= len(polynomial):
            break
        if coefficient:
            total += coefficient * poly_evaluate(derivative, point) / math.factorial(r)
        derivative = poly_derivative(derivative)
    return total


# ---------------------------------------------------------------------------
# Exact dyadic values of F and up
# ---------------------------------------------------------------------------


def inverse_power_values(max_level: int) -> list[Fraction]:
    r"""Return V_n=F(2^{-n}) exactly, 0<=n<=max_level.

    This is the triangular recurrence used throughout the ProveIt corpus:

      V_n = [sum_{k<n} 2^{k(k-1)/2} V_k/(n-k+1)!]
            / [2^{n(n-1)/2}(2^n-1)].
    """

    values = [Fraction(1)]  # V_0=F(1)=1
    for n in range(1, max_level + 1):
        total = Fraction(0)
        for k in range(n):
            total += (
                Fraction(2 ** (k * (k - 1) // 2), math.factorial(n - k + 1))
                * values[k]
            )
        denominator = 2 ** (n * (n - 1) // 2) * (2**n - 1)
        values.append(total / denominator)
    return values


def exact_dyadic_fabius_table(
    exponent: int, inverse_values: Sequence[Fraction]
) -> list[Fraction]:
    r"""Return F(a/2^exponent), 0<=a<=2^exponent, exactly.

    The terminating highest-bit/Taylor-block recursion is independent of the
    interpolation and synthesis calculations, making it a useful exact check.
    """

    denominator = 1 << exponent
    values = [Fraction(0)] * (denominator + 1)
    values[denominator] = Fraction(1)

    for a in range(1, denominator):
        highest_bit = a.bit_length() - 1
        order = exponent - highest_bit
        remainder = a - (1 << highest_bit)
        y = Fraction(remainder, denominator)

        block = Fraction(0)
        y_power = Fraction(1)
        factorial = 1
        for j in range(order + 1):
            if j:
                y_power *= y
                factorial *= j
            block += (
                Fraction(2 ** (j * (j + 1) // 2), factorial)
                * inverse_values[order - j]
                * y_power
            )
        values[a] = block - values[remainder]
    return values


def up_at_dyadic(
    point: Fraction, exponent: int, fabius_table: Sequence[Fraction]
) -> Fraction:
    r"""Evaluate up(point) exactly when its denominator divides 2^exponent.

    On [-1,1], evenness and up(t)=F(1+t) for -1<=t<=0 give

        up(t)=F(1-|t|).
    """

    if point < -1 or point > 1:
        return Fraction(0)
    argument = Fraction(1) - abs(point)
    index = argument * (1 << exponent)
    if index.denominator != 1:
        raise ValueError("point is not on the requested dyadic grid")
    return fabius_table[index.numerator]


# ---------------------------------------------------------------------------
# Exact Btilde and D matrices
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ExactLoopMatrices:
    degree: int
    m: int
    nodes: tuple[Fraction, ...]
    shift_indices: tuple[int, ...]
    decoder: tuple[tuple[Fraction, ...], ...]  # D[k,j]
    kernel: tuple[tuple[Fraction, ...], ...]  # Btilde[i,k]


def is_power_of_two(value: int) -> bool:
    return value > 0 and (value & (value - 1)) == 0


def build_exact_equispaced_loop(degree: int) -> ExactLoopMatrices:
    """Build exact matrices for a power-of-two equispaced degree."""

    if not is_power_of_two(degree):
        raise ValueError("exact equispaced check requires a power-of-two degree")

    m = 1 << degree
    h = Fraction(1, m)
    nodes = tuple(Fraction(-1) + Fraction(2 * j, degree) for j in range(degree + 1))
    shifts = tuple(range(-2 * m + 1, 2 * m))
    gamma = gamma_coefficients(degree)
    cardinals = [lagrange_polynomial_exact(nodes, j) for j in range(degree + 1)]

    decoder = tuple(
        tuple(
            appell_evaluate_exact(cardinals[j], Fraction(k, m), gamma)
            for j in range(degree + 1)
        )
        for k in shifts
    )

    # Every node and every shift center has denominator dividing 2^degree.
    inverse_values = inverse_power_values(degree)
    fabius_table = exact_dyadic_fabius_table(degree, inverse_values)
    kernel = tuple(
        tuple(
            h * up_at_dyadic(nodes[i] - Fraction(k, m), degree, fabius_table)
            for k in shifts
        )
        for i in range(degree + 1)
    )
    return ExactLoopMatrices(degree, m, nodes, shifts, decoder, kernel)


def exact_matrix_product(
    left: Sequence[Sequence[Fraction]], right: Sequence[Sequence[Fraction]]
) -> list[list[Fraction]]:
    rows = len(left)
    inner = len(right)
    columns = len(right[0])
    return [
        [
            sum((left[i][k] * right[k][j] for k in range(inner)), Fraction(0))
            for j in range(columns)
        ]
        for i in range(rows)
    ]


def exact_loop_diagnostics(degree: int) -> dict[str, object]:
    matrices = build_exact_equispaced_loop(degree)
    identity = exact_matrix_product(matrices.kernel, matrices.decoder)
    verified = all(
        identity[i][j] == (1 if i == j else 0)
        for i in range(degree + 1)
        for j in range(degree + 1)
    )

    decoder_row_sums = [sum(row, Fraction(0)) for row in matrices.decoder]
    kernel_row_sums = [sum(row, Fraction(0)) for row in matrices.kernel]
    unital_verified = all(value == 1 for value in decoder_row_sums + kernel_row_sums)

    decoder_row_l1 = [sum((abs(value) for value in row), Fraction(0)) for row in matrices.decoder]
    max_decoder_l1 = max(decoder_row_l1)
    max_decoder_index = matrices.shift_indices[decoder_row_l1.index(max_decoder_l1)]

    pair_bounds: list[Fraction] = []
    pair_tvs: list[Fraction] = []
    for i in range(degree):
        l1_distance = sum(
            (
                abs(matrices.kernel[i][k] - matrices.kernel[i + 1][k])
                for k in range(len(matrices.shift_indices))
            ),
            Fraction(0),
        )
        pair_tvs.append(l1_distance / 2)
        pair_bounds.append(Fraction(2) / l1_distance)

    max_num_bits = max(
        abs(value.numerator).bit_length()
        for row in matrices.decoder
        for value in row
    )
    max_den_bits = max(
        value.denominator.bit_length()
        for row in matrices.decoder
        for value in row
    )

    return {
        "degree": degree,
        "m": matrices.m,
        "shift_count": len(matrices.shift_indices),
        "right_inverse_exact": verified,
        "row_unital_exact": unital_verified,
        "max_decoder_row_l1": float(max_decoder_l1),
        "max_decoder_row_l1_exact": str(max_decoder_l1),
        "max_decoder_row_shift_index": max_decoder_index,
        "adjacent_tv": float(min(pair_tvs)) if pair_tvs else 1.0,
        "two_row_lower_bound": float(max(pair_bounds)) if pair_bounds else 1.0,
        "max_numerator_bits": max_num_bits,
        "max_denominator_bits": max_den_bits,
    }


# ---------------------------------------------------------------------------
# Independent Fourier evaluator for up
# ---------------------------------------------------------------------------


def sinc(value: float) -> float:
    return 1.0 if value == 0.0 else math.sin(value) / value


def phi_product(value: float, factors: int = 120) -> float:
    r"""Evaluate Phi(t)=product_{j>=1} sinc(t/2^j)."""

    result = 1.0
    scale = 2.0
    for _ in range(factors):
        result *= sinc(value / scale)
        scale *= 2.0
    return result


def odd_fourier_coefficients(modes: int = 256) -> np.ndarray:
    r"""Return Phi((2r+1)pi), the period-two cosine coefficients of up."""

    return np.asarray(
        [phi_product((2 * r + 1) * math.pi) for r in range(modes)],
        dtype=float,
    )


def up_values(
    points: np.ndarray | Sequence[float] | float,
    coefficients: np.ndarray,
    chunk_size: int = 50_000,
) -> np.ndarray:
    r"""Evaluate up from its independent period-two cosine series.

      up(x)=1/2+sum_{r>=0} Phi((2r+1)pi) cos((2r+1)pi x), |x|<=1.

    The 256-mode tail is below roughly 1.4e-16 in absolute coefficient
    sum for the parameters used here.
    """

    array = np.asarray(points, dtype=float)
    flat = array.reshape(-1)
    result = np.zeros_like(flat)
    inside = np.abs(flat) <= 1.0
    inside_values = flat[inside]
    frequencies = (2 * np.arange(coefficients.size) + 1) * math.pi

    evaluated = np.empty_like(inside_values)
    for start in range(0, inside_values.size, chunk_size):
        stop = min(start + chunk_size, inside_values.size)
        phase = np.outer(inside_values[start:stop], frequencies)
        evaluated[start:stop] = 0.5 + np.cos(phase) @ coefficients

    # The exact endpoint value is zero.  Pinning it avoids a harmless ulp-scale
    # Fourier residual from polluting exact-node interpolation tests.
    evaluated[np.isclose(np.abs(inside_values), 1.0, rtol=0.0, atol=2e-15)] = 0.0
    result[inside] = evaluated
    return result.reshape(array.shape)


# ---------------------------------------------------------------------------
# Floating matrices and reduced projector singular values
# ---------------------------------------------------------------------------


def lagrange_polynomial_float(nodes: np.ndarray, index: int) -> Polynomial:
    roots = np.delete(nodes, index)
    numerator = Polynomial.fromroots(roots)
    denominator = np.prod(nodes[index] - roots)
    return numerator / denominator


def appell_values_float(
    polynomial: Polynomial, points: np.ndarray, gamma: Sequence[Fraction]
) -> np.ndarray:
    total = np.zeros_like(points, dtype=float)
    derivative = polynomial
    for r, coefficient in enumerate(gamma):
        if r > polynomial.degree():
            break
        if coefficient:
            total += float(coefficient) * derivative(points) / math.factorial(r)
        derivative = derivative.deriv()
    return total


def interpolation_nodes(degree: int, kind: str) -> np.ndarray:
    if kind == "equispaced":
        return np.linspace(-1.0, 1.0, degree + 1)
    if kind == "chebyshev":
        # Ascending Chebyshev--Lobatto nodes.  The sets are nested when degree
        # runs through powers of two.
        return np.sort(np.cos(math.pi * np.arange(degree + 1) / degree))
    raise ValueError(f"unknown node kind: {kind}")


def build_floating_loop(
    degree: int, kind: str, fourier_coefficients: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    """Return normalized Btilde and D without forming the projector."""

    m = 1 << degree
    h = 1.0 / m
    shift_indices = np.arange(-2 * m + 1, 2 * m, dtype=int)
    shift_centers = shift_indices * h
    nodes = interpolation_nodes(degree, kind)
    gamma = gamma_coefficients(degree)

    decoder = np.empty((shift_centers.size, degree + 1), dtype=float)
    for j in range(degree + 1):
        cardinal = lagrange_polynomial_float(nodes, j)
        decoder[:, j] = appell_values_float(cardinal, shift_centers, gamma)

    kernel = h * up_values(
        nodes[:, None] - shift_centers[None, :], fourier_coefficients
    )
    return kernel, decoder


def projector_diagnostics(
    degree: int, kind: str, fourier_coefficients: np.ndarray
) -> dict[str, object]:
    start = time.perf_counter()
    kernel, decoder = build_floating_loop(degree, kind, fourier_coefficients)
    residual = kernel @ decoder - np.eye(degree + 1)

    # Thin QR factorizations reduce the singular-value problem from an
    # (4*2^n-1)-square projector to an (n+1)-square matrix.
    _, r_decoder = np.linalg.qr(decoder, mode="reduced")
    _, r_kernel = np.linalg.qr(kernel.T, mode="reduced")
    nonzero_singular_values = np.linalg.svd(
        r_decoder @ r_kernel.T, compute_uv=False
    )

    return {
        "degree": degree,
        "node_kind": kind,
        "m": 1 << degree,
        "shift_count": 4 * (1 << degree) - 1,
        "right_inverse_residual_inf": float(np.linalg.norm(residual, ord=np.inf)),
        "projector_norm_2": float(nonzero_singular_values[0]),
        "smallest_nonzero_projector_singular_value": float(nonzero_singular_values[-1]),
        "decoder_norm_2": float(np.linalg.svd(decoder, compute_uv=False)[0]),
        "kernel_norm_2": float(np.linalg.svd(kernel, compute_uv=False)[0]),
        "max_abs_decoder_entry": float(np.max(np.abs(decoder))),
        "max_decoder_row_l1": float(np.max(np.sum(np.abs(decoder), axis=1))),
        "elapsed_seconds": time.perf_counter() - start,
    }


# ---------------------------------------------------------------------------
# Barycentric interpolation experiments
# ---------------------------------------------------------------------------


def barycentric_weights(degree: int, kind: str) -> np.ndarray:
    if kind == "equispaced":
        weights = np.asarray(
            [(-1.0) ** j * math.comb(degree, j) for j in range(degree + 1)],
            dtype=float,
        )
        return weights / np.max(np.abs(weights))
    if kind == "chebyshev":
        weights = (-1.0) ** np.arange(degree + 1)
        weights[0] *= 0.5
        weights[-1] *= 0.5
        return weights
    raise ValueError(f"unknown node kind: {kind}")


def barycentric_evaluate(
    nodes: np.ndarray,
    values: np.ndarray,
    weights: np.ndarray,
    points: np.ndarray,
    chunk_size: int = 8192,
) -> np.ndarray:
    """Evaluate a barycentric interpolant, explicitly handling node hits."""

    output = np.empty_like(points, dtype=float)
    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        for start in range(0, points.size, chunk_size):
            stop = min(start + chunk_size, points.size)
            x = points[start:stop]
            differences = x[:, None] - nodes[None, :]
            hits = np.isclose(differences, 0.0, rtol=0.0, atol=2e-15)
            safe = ~hits
            numerator = np.sum(
                np.divide(
                    (weights * values)[None, :],
                    differences,
                    out=np.zeros_like(differences),
                    where=safe,
                ),
                axis=1,
            )
            denominator = np.sum(
                np.divide(
                    weights[None, :],
                    differences,
                    out=np.zeros_like(differences),
                    where=safe,
                ),
                axis=1,
            )
            result = numerator / denominator
            hit_rows = np.nonzero(np.any(hits, axis=1))[0]
            for row in hit_rows:
                result[row] = values[np.nonzero(hits[row])[0][0]]
            output[start:stop] = result
    return output


def exact_equispaced_up_samples(degree: int) -> tuple[list[Fraction], list[Fraction]]:
    """Exact samples at -1+2j/degree for a power-of-two degree."""

    if not is_power_of_two(degree):
        raise ValueError("degree must be a power of two")
    node_exponent = max(int(math.log2(degree)) - 1, 0)
    inverse_values = inverse_power_values(node_exponent)
    table = exact_dyadic_fabius_table(node_exponent, inverse_values)
    nodes = [Fraction(-1) + Fraction(2 * j, degree) for j in range(degree + 1)]
    values = [up_at_dyadic(node, node_exponent, table) for node in nodes]
    return nodes, values


def barycentric_equispaced_mp_at(
    degree: int,
    points: Iterable[float],
    decimal_digits: int = 140,
) -> list[mp.mpf]:
    """High-precision barycentric values from exact dyadic sample data."""

    rational_nodes, rational_values = exact_equispaced_up_samples(degree)
    mp.mp.dps = decimal_digits
    nodes = [mp.mpf(v.numerator) / v.denominator for v in rational_nodes]
    values = [mp.mpf(v.numerator) / v.denominator for v in rational_values]
    weights = [mp.mpf((-1) ** j * math.comb(degree, j)) for j in range(degree + 1)]

    answer: list[mp.mpf] = []
    for point in points:
        x = mp.mpf(str(float(point)))
        node_index = next((i for i, node in enumerate(nodes) if x == node), None)
        if node_index is not None:
            answer.append(values[node_index])
            continue
        numerator = mp.fsum(
            weight * value / (x - node)
            for weight, value, node in zip(weights, values, nodes)
        )
        denominator = mp.fsum(weight / (x - node) for weight, node in zip(weights, nodes))
        answer.append(numerator / denominator)
    return answer


def high_precision_equispaced_error(
    degree: int,
    fourier_coefficients: np.ndarray,
    coarse_points: int = 2400,
    refine_points: int = 2400,
) -> dict[str, object]:
    """Locate the endpoint Runge peak using exact data and mp arithmetic.

    Evenness lets us scan only [0,1].  The first coarse grid is uniform; a
    second grid refines the best coarse cell.  This is a sampled maximum, not
    a certified continuum extremum, and the CSV labels it accordingly.
    """

    coarse = np.linspace(0.0, 1.0 - 1e-8, coarse_points)
    coarse_values_mp = barycentric_equispaced_mp_at(degree, coarse)
    coarse_values = np.asarray([float(value) for value in coarse_values_mp])
    coarse_truth = up_values(coarse, fourier_coefficients)
    coarse_error = np.abs(coarse_values - coarse_truth)
    best = int(np.argmax(coarse_error))

    left = coarse[max(0, best - 1)]
    right = coarse[min(coarse.size - 1, best + 1)]
    refined = np.linspace(left, right, refine_points)
    refined_values_mp = barycentric_equispaced_mp_at(degree, refined)
    refined_values = np.asarray([float(value) for value in refined_values_mp])
    refined_truth = up_values(refined, fourier_coefficients)
    refined_error = np.abs(refined_values - refined_truth)
    best_refined = int(np.argmax(refined_error))

    return {
        "degree": degree,
        "node_kind": "equispaced",
        "sampled_sup_error": float(refined_error[best_refined]),
        "sampled_peak_location_abs": float(refined[best_refined]),
        "sampled_peak_value": float(refined_values[best_refined]),
        "arithmetic": "exact dyadic data; 140-digit barycentric evaluation",
    }


def ordinary_interpolation_error(
    degree: int,
    kind: str,
    fourier_coefficients: np.ndarray,
    grid_points: int = 32769,
) -> dict[str, object]:
    nodes = interpolation_nodes(degree, kind)
    data = up_values(nodes, fourier_coefficients)
    weights = barycentric_weights(degree, kind)
    grid = np.linspace(-1.0, 1.0, grid_points)
    target = up_values(grid, fourier_coefficients)
    interpolant = barycentric_evaluate(nodes, data, weights, grid)
    error = np.abs(interpolant - target)
    best = int(np.nanargmax(error))
    return {
        "degree": degree,
        "node_kind": kind,
        "sampled_sup_error": float(error[best]),
        "sampled_peak_location_abs": float(abs(grid[best])),
        "sampled_peak_value": float(interpolant[best]),
        "arithmetic": "double barycentric/Fourier",
    }


# ---------------------------------------------------------------------------
# Concrete degree-two identity
# ---------------------------------------------------------------------------


def degree_two_example() -> dict[str, object]:
    r"""Return the closed loop generated by nodes -1,0,1.

    Since up(-1)=up(1)=0 and up(0)=1, I_2 up=1-x^2.  Here

        A(1-x^2)=10/9-x^2,

    hence, on [-1,1],

        1-x^2 = sum_{k=-7}^7 (5/18-k^2/64) up(x-k/4).
    """

    coefficients = {
        str(k): str(Fraction(5, 18) - Fraction(k * k, 64))
        for k in range(-7, 8)
    }
    return {
        "interpolant": "1 - x^2",
        "shift_grid": "k/4, -7 <= k <= 7",
        "coefficient_formula": "5/18 - k^2/64",
        "coefficients": coefficients,
    }


# ---------------------------------------------------------------------------
# Output helpers and main program
# ---------------------------------------------------------------------------


def write_csv(path: Path, rows: Sequence[dict[str, object]]) -> None:
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def make_projector_figure(rows: Sequence[dict[str, object]]) -> None:
    fig, ax = plt.subplots(figsize=(7.2, 4.5))
    for kind in ("equispaced", "chebyshev"):
        selected = [row for row in rows if row["node_kind"] == kind]
        ax.semilogy(
            [int(row["degree"]) for row in selected],
            [float(row["projector_norm_2"]) for row in selected],
            marker="o",
            label=kind.capitalize(),
        )
    ax.set_xlabel("Polynomial degree n")
    ax.set_ylabel(r"Coefficient projector norm $\|P_n\|_2$")
    ax.set_title("Obliquity of the exact coefficient-space projector")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(FIGURES / "projector_obliquity.pdf")
    fig.savefig(FIGURES / "projector_obliquity.png", dpi=180)
    plt.close(fig)


def make_interpolation_figure(rows: Sequence[dict[str, object]]) -> None:
    fig, ax = plt.subplots(figsize=(7.2, 4.5))
    for kind in ("equispaced", "chebyshev"):
        selected = [row for row in rows if row["node_kind"] == kind]
        ax.semilogy(
            [int(row["degree"]) for row in selected],
            [float(row["sampled_sup_error"]) for row in selected],
            marker="o",
            label=kind.capitalize(),
        )
    ax.set_xlabel("Polynomial degree n")
    ax.set_ylabel("Sampled uniform interpolation error")
    ax.set_title("The up-shift loop inherits the Lagrange error exactly")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(FIGURES / "interpolation_error.pdf")
    fig.savefig(FIGURES / "interpolation_error.png", dpi=180)
    plt.close(fig)


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--quick",
        action="store_true",
        help="skip the largest matrices and high-precision n=64 Runge scan",
    )
    return parser.parse_args()


def main() -> None:
    arguments = parse_arguments()
    start = time.perf_counter()
    fourier_coefficients = odd_fourier_coefficients(256)

    exact_degrees = [1, 2, 4] if arguments.quick else [1, 2, 4, 8]
    exact_rows = [exact_loop_diagnostics(degree) for degree in exact_degrees]
    write_csv(RESULTS / "exact_right_inverse_checks.csv", exact_rows)

    matrix_degrees = [2, 4, 6, 8] if arguments.quick else [2, 4, 6, 8, 10, 12]
    projector_rows: list[dict[str, object]] = []
    for kind in ("equispaced", "chebyshev"):
        for degree in matrix_degrees:
            projector_rows.append(
                projector_diagnostics(degree, kind, fourier_coefficients)
            )
    write_csv(RESULTS / "projector_obliquity.csv", projector_rows)
    make_projector_figure(projector_rows)

    interpolation_rows: list[dict[str, object]] = []
    for degree in [4, 8, 16, 32, 64, 128]:
        interpolation_rows.append(
            ordinary_interpolation_error(
                degree, "chebyshev", fourier_coefficients
            )
        )

    equispaced_degrees = [4, 8, 16, 32] if arguments.quick else [4, 8, 16, 32, 64]
    for degree in equispaced_degrees:
        if degree <= 16:
            interpolation_rows.append(
                ordinary_interpolation_error(
                    degree, "equispaced", fourier_coefficients
                )
            )
        else:
            interpolation_rows.append(
                high_precision_equispaced_error(
                    degree, fourier_coefficients,
                    coarse_points=1200 if arguments.quick else 2400,
                    refine_points=1200 if arguments.quick else 2400,
                )
            )

    interpolation_rows.sort(key=lambda row: (str(row["node_kind"]), int(row["degree"])))
    write_csv(RESULTS / "interpolation_errors.csv", interpolation_rows)
    make_interpolation_figure(interpolation_rows)

    metadata = {
        "formula_snapshot_commit": "4544e9af6b94820402c69967be1dff3f85e43c1e",
        "fourier_modes": 256,
        "fourier_omitted_absolute_coefficient_sum_estimate": float(
            sum(abs(phi_product((2 * r + 1) * math.pi)) for r in range(256, 512))
        ),
        "degree_two_example": degree_two_example(),
        "elapsed_seconds": time.perf_counter() - start,
        "quick_mode": bool(arguments.quick),
    }
    (RESULTS / "metadata.json").write_text(
        json.dumps(metadata, indent=2), encoding="utf-8"
    )

    print(json.dumps({
        "exact_checks": exact_rows,
        "projector_rows": len(projector_rows),
        "interpolation_rows": len(interpolation_rows),
        "elapsed_seconds": metadata["elapsed_seconds"],
    }, indent=2))


if __name__ == "__main__":
    main()
