#!/usr/bin/env python3
"""Numerical experiments for dyadic-comb interpolation of Fabius/Rvachev.

The script is deliberately self-contained.  It uses exact rational arithmetic for every
Fabius value on a dyadic grid, and arbitrary-precision arithmetic only for evaluating the
interpolating polynomials.  This separation is important: the spectacular values produced
by equispaced interpolation are genuine Runge oscillations, not contamination from an
approximate Fabius oracle.

Main experiments
----------------
* ordinary global Lagrange interpolation on x_j=j/N, N=2^n;
* endpoint-flat Hermite interpolation, matching every value and the first m derivatives
  (all zero) at 0 and 1;
* the analogous construction for up(2x-1);
* first-derivative Hermite interpolation at every dyadic node;
* weighted Lebesgue constants and the two explicit cardinal-mode lower bounds;
* exact endpoint derivative defects of the ordinary interpolant.

Examples
--------
  python numerical_experiments.py --task smoke
  python numerical_experiments.py --task fabius --N 64 --m-start 0 --m-end 18
  python numerical_experiments.py --task up --N 64 --m-start 0 --m-end 20
  python numerical_experiments.py --task hermite --N-list 4,8,16,32,64
  python numerical_experiments.py --task derivative --n-min 4 --n-max 14
  python numerical_experiments.py --task predictions --N-list 8,16,32,64,128,256
  python numerical_experiments.py --task lebesgue --N 64 --m-start 0 --m-end 24
  python numerical_experiments.py --task figures --data-dir data --figure-dir figures

All generated CSV files use decimal strings with enough significant digits to reproduce the
printed tables.  The plotting task reads those CSV files and uses Matplotlib's default color
cycle; no external style or TeX installation is required for the plots themselves.
"""

from __future__ import annotations

import argparse
import csv
import math
import sys
import time

# Python 3.11 guards conversions of very large integers to decimal strings.  The exact
# dyadic experiments intentionally exceed that default; disable the guard for this trusted
# local computation.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Callable, Iterable, Sequence

import mpmath as mp


# ---------------------------------------------------------------------------
# Exact dyadic Fabius arithmetic
# ---------------------------------------------------------------------------


class DyadicFabius:
    """Exact evaluator for F(a/2^e), based on the audited repository recurrence."""

    def __init__(self) -> None:
        self._V: list[Fraction] = [Fraction(1)]  # V_n = F(2^{-n})

    def ensure_inverse_powers(self, max_n: int) -> None:
        """Extend the table V_n=F(2^{-n}) through max_n, exactly."""
        while len(self._V) <= max_n:
            n = len(self._V)
            total = Fraction(0)
            for k in range(n):
                total += (
                    Fraction(2 ** (k * (k - 1) // 2), math.factorial(n - k + 1))
                    * self._V[k]
                )
            denominator = 2 ** (n * (n - 1) // 2) * (2**n - 1)
            self._V.append(total / denominator)

    def inverse_power(self, n: int) -> Fraction:
        self.ensure_inverse_powers(n)
        return self._V[n]

    @lru_cache(maxsize=None)
    def value(self, exponent: int, numerator: int) -> Fraction:
        """Return F(numerator/2**exponent) exactly for 0 <= numerator <= 2**exponent.

        Values outside [0,1] are clipped here because all experiments call the bounded
        distribution function rather than the signed global extension.
        """
        if exponent < 0:
            raise ValueError("exponent must be nonnegative")
        denominator = 1 << exponent
        if numerator <= 0:
            return Fraction(0)
        if numerator >= denominator:
            return Fraction(1)

        # Remove the leading binary one.  This is the bit recursion stated in the main
        # Fabius/Rvachev synthesis document.
        leading_bit = numerator.bit_length() - 1
        r = exponent - leading_bit
        remainder = numerator - (1 << leading_bit)
        y = Fraction(remainder, denominator)
        self.ensure_inverse_powers(r)

        taylor_block = Fraction(0)
        for j in range(r + 1):
            taylor_block += (
                Fraction(2 ** (j * (j + 1) // 2), math.factorial(j))
                * self._V[r - j]
                * y**j
            )
        return taylor_block - self.value(exponent, remainder)

    def up_on_unit_interval(self, exponent: int, numerator: int) -> Fraction:
        """Return up(2x-1) at x=numerator/2**exponent, exactly."""
        denominator = 1 << exponent
        if numerator <= 0 or numerator >= denominator:
            return Fraction(0)
        folded = min(numerator, denominator - numerator)
        # 1-|2x-1| = 2 min(x,1-x).
        return self.value(exponent - 1, folded)


FABIUS = DyadicFabius()


def mp_from_fraction(q: Fraction) -> mp.mpf:
    return mp.mpf(q.numerator) / q.denominator


# ---------------------------------------------------------------------------
# Endpoint-flat Hermite bridge and barycentric evaluation
# ---------------------------------------------------------------------------


def beta_smoothstep_fraction(m: int, x: Fraction) -> Fraction:
    r"""The polynomial S_m(x)=I_x(m+1,m+1), evaluated exactly.

    S_m(0)=0, S_m(1)=1, and S_m^(r)(0)=S_m^(r)(1)=0 for 1<=r<=m.
    """
    if m < 0:
        raise ValueError("m must be nonnegative")
    normalizer = Fraction(math.factorial(2 * m + 1), math.factorial(m) ** 2)
    total = Fraction(0)
    for r in range(m + 1):
        total += Fraction((-1) ** r * math.comb(m, r), m + r + 1) * x ** (
            m + r + 1
        )
    return normalizer * total


def beta_smoothstep_mpf(m: int, x: mp.mpf) -> mp.mpf:
    normalizer = mp.mpf(math.factorial(2 * m + 1)) / math.factorial(m) ** 2
    terms = [
        mp.mpf((-1) ** r * math.comb(m, r)) / (m + r + 1) * x ** (m + r + 1)
        for r in range(m + 1)
    ]
    return normalizer * mp.fsum(terms)


def endpoint_weight_fraction(m: int, x: Fraction) -> Fraction:
    return (x * (1 - x)) ** (m + 1)


def endpoint_weight_mpf(m: int, x: mp.mpf) -> mp.mpf:
    return (x * (1 - x)) ** (m + 1)


@dataclass(frozen=True)
class BarycentricData:
    nodes: tuple[mp.mpf, ...]
    values: tuple[mp.mpf, ...]
    weights: tuple[mp.mpf, ...]


def barycentric_evaluate(data: BarycentricData, x: mp.mpf) -> mp.mpf:
    for node, value in zip(data.nodes, data.values):
        if x == node:
            return value
    terms = [w / (x - node) for node, w in zip(data.nodes, data.weights)]
    denominator = mp.fsum(terms)
    numerator = mp.fsum(t * value for t, value in zip(terms, data.values))
    return numerator / denominator


def interior_barycentric_weights(N: int) -> tuple[mp.mpf, ...]:
    """Weights for nodes j/N, j=1,...,N-1, scaled by a harmless common factor."""
    if N < 2:
        raise ValueError("N must be at least 2")
    maximum = math.comb(N - 2, (N - 2) // 2)
    return tuple(
        mp.mpf((-1) ** (j - 1) * math.comb(N - 2, j - 1)) / maximum
        for j in range(1, N)
    )


def full_barycentric_weights(N: int) -> tuple[mp.mpf, ...]:
    maximum = math.comb(N, N // 2)
    return tuple(
        mp.mpf((-1) ** j * math.comb(N, j)) / maximum for j in range(N + 1)
    )


@dataclass(frozen=True)
class EndpointFlatInterpolant:
    N: int
    m: int
    target: str
    quotient: BarycentricData

    @property
    def degree(self) -> int:
        return self.N + 2 * self.m

    def __call__(self, x: mp.mpf) -> mp.mpf:
        if self.target == "fabius":
            if x == 0:
                return mp.mpf(0)
            if x == 1:
                return mp.mpf(1)
            bridge = beta_smoothstep_mpf(self.m, x)
        elif self.target == "up":
            if x == 0 or x == 1:
                return mp.mpf(0)
            bridge = mp.mpf(0)
        else:
            raise ValueError(f"unknown target {self.target!r}")
        return bridge + endpoint_weight_mpf(self.m, x) * barycentric_evaluate(
            self.quotient, x
        )


def build_endpoint_flat_interpolant(
    target: str, N: int, m: int, dps: int
) -> EndpointFlatInterpolant:
    if N <= 1 or N & (N - 1):
        raise ValueError("N must be a power of two at least 2")
    if m < 0:
        raise ValueError("m must be nonnegative")
    mp.mp.dps = dps
    exponent = N.bit_length() - 1
    nodes = tuple(mp.mpf(j) / N for j in range(1, N))
    values: list[mp.mpf] = []
    for j in range(1, N):
        xq = Fraction(j, N)
        if target == "fabius":
            sample = FABIUS.value(exponent, j)
            bridge = beta_smoothstep_fraction(m, xq)
        elif target == "up":
            sample = FABIUS.up_on_unit_interval(exponent, j)
            bridge = Fraction(0)
        else:
            raise ValueError("target must be 'fabius' or 'up'")
        denominator = endpoint_weight_fraction(m, xq)
        values.append(mp_from_fraction((sample - bridge) / denominator))
    data = BarycentricData(nodes, tuple(values), interior_barycentric_weights(N))
    return EndpointFlatInterpolant(N, m, target, data)


# ---------------------------------------------------------------------------
# First-derivative Hermite interpolation at every node
# ---------------------------------------------------------------------------


def harmonic_number(k: int) -> mp.mpf:
    return mp.fsum(mp.mpf(1) / j for j in range(1, k + 1)) if k else mp.mpf(0)


@dataclass(frozen=True)
class FirstHermiteInterpolant:
    N: int
    nodes: tuple[mp.mpf, ...]
    values: tuple[mp.mpf, ...]
    derivatives: tuple[mp.mpf, ...]
    weights: tuple[mp.mpf, ...]
    cardinal_slopes: tuple[mp.mpf, ...]

    @property
    def degree(self) -> int:
        return 2 * self.N + 1

    def __call__(self, x: mp.mpf) -> mp.mpf:
        for node, value in zip(self.nodes, self.values):
            if x == node:
                return value
        raw = [w / (x - node) for node, w in zip(self.nodes, self.weights)]
        denominator = mp.fsum(raw)
        cardinal = [t / denominator for t in raw]
        return mp.fsum(
            (1 - 2 * slope * (x - node)) * ell**2 * value
            + (x - node) * ell**2 * derivative
            for node, value, derivative, ell, slope in zip(
                self.nodes,
                self.values,
                self.derivatives,
                cardinal,
                self.cardinal_slopes,
            )
        )


def build_first_hermite_interpolant(N: int, dps: int) -> FirstHermiteInterpolant:
    if N <= 1 or N & (N - 1):
        raise ValueError("N must be a power of two")
    mp.mp.dps = dps
    exponent = N.bit_length() - 1
    nodes = tuple(mp.mpf(j) / N for j in range(N + 1))
    values = tuple(mp_from_fraction(FABIUS.value(exponent, j)) for j in range(N + 1))
    derivatives: list[mp.mpf] = []
    for j in range(N + 1):
        if j == 0 or j == N:
            derivative = Fraction(0)
        elif 2 * j <= N:
            derivative = 2 * FABIUS.value(exponent - 1, j)
        else:
            derivative = 2 * FABIUS.value(exponent - 1, N - j)
        derivatives.append(mp_from_fraction(derivative))
    slopes = tuple(
        N * (harmonic_number(j) - harmonic_number(N - j)) for j in range(N + 1)
    )
    return FirstHermiteInterpolant(
        N,
        nodes,
        values,
        tuple(derivatives),
        full_barycentric_weights(N),
        slopes,
    )


# ---------------------------------------------------------------------------
# Error scans and condition numbers
# ---------------------------------------------------------------------------


def precision_for(N: int, m: int = 0) -> int:
    # Deliberately generous.  The largest experiments in the report remain fast enough.
    return max(120, 3 * N + 5 * m)


def exact_target(target: str, exponent: int, numerator: int) -> Fraction:
    if target == "fabius":
        return FABIUS.value(exponent, numerator)
    if target == "up":
        return FABIUS.up_on_unit_interval(exponent, numerator)
    raise ValueError(target)


def scan_error(
    interpolant: Callable[[mp.mpf], mp.mpf],
    target: str,
    N: int,
    m: int,
    grid_level: int,
) -> dict[str, str | int]:
    maximum_error = mp.mpf(0)
    maximum_x = mp.mpf(0)
    minimum_value = mp.inf
    maximum_value = -mp.inf
    boundary_error = mp.mpf(0)
    boundary_width = mp.mpf(2) / N
    denominator = 1 << grid_level

    for numerator in range(denominator + 1):
        x = mp.mpf(numerator) / denominator
        p = interpolant(x)
        f = mp_from_fraction(exact_target(target, grid_level, numerator))
        error = abs(p - f)
        if error > maximum_error:
            maximum_error = error
            maximum_x = x
        if x <= boundary_width or x >= 1 - boundary_width:
            boundary_error = max(boundary_error, error)
        minimum_value = min(minimum_value, p)
        maximum_value = max(maximum_value, p)

    return {
        "function": target,
        "N": N,
        "m": m,
        "degree": N + 2 * m,
        "grid_level": grid_level,
        "max_abs_error": mp.nstr(maximum_error, 28),
        "argmax": mp.nstr(maximum_x, 18),
        "max_boundary_error": mp.nstr(boundary_error, 28),
        "min_interpolant": mp.nstr(minimum_value, 28),
        "max_interpolant": mp.nstr(maximum_value, 28),
    }


def scan_first_hermite(N: int, grid_level: int) -> dict[str, str | int]:
    dps = precision_for(N, N // 2)
    interpolant = build_first_hermite_interpolant(N, dps)
    maximum_error = mp.mpf(0)
    maximum_x = mp.mpf(0)
    minimum_value = mp.inf
    maximum_value = -mp.inf
    denominator = 1 << grid_level
    for numerator in range(denominator + 1):
        x = mp.mpf(numerator) / denominator
        p = interpolant(x)
        f = mp_from_fraction(FABIUS.value(grid_level, numerator))
        error = abs(p - f)
        if error > maximum_error:
            maximum_error, maximum_x = error, x
        minimum_value = min(minimum_value, p)
        maximum_value = max(maximum_value, p)
    return {
        "N": N,
        "degree": interpolant.degree,
        "grid_level": grid_level,
        "max_abs_error": mp.nstr(maximum_error, 28),
        "argmax": mp.nstr(maximum_x, 18),
        "min_interpolant": mp.nstr(minimum_value, 28),
        "max_interpolant": mp.nstr(maximum_value, 28),
    }


def weighted_lebesgue_maximum(N: int, m: int, grid_level: int) -> dict[str, str | int]:
    mp.mp.dps = precision_for(N, m)
    nodes = tuple(mp.mpf(j) / N for j in range(1, N))
    weights = interior_barycentric_weights(N)
    node_weights = tuple(endpoint_weight_mpf(m, node) for node in nodes)
    maximum = mp.mpf(1)
    maximum_x = nodes[0]
    denominator_grid = 1 << grid_level

    for numerator in range(1, denominator_grid):
        # Original nodes have Lebesgue value exactly one; skip them to avoid 0/0.
        if (numerator * N) % denominator_grid == 0:
            continue
        x = mp.mpf(numerator) / denominator_grid
        raw = [w / (x - node) for node, w in zip(nodes, weights)]
        denominator = mp.fsum(raw)
        wx = endpoint_weight_mpf(m, x)
        value = mp.fsum(
            abs(wx / wj * term / denominator)
            for wj, term in zip(node_weights, raw)
        )
        if value > maximum:
            maximum, maximum_x = value, x
    return {
        "N": N,
        "m": m,
        "grid_level": grid_level,
        "max_weighted_lebesgue": mp.nstr(maximum, 28),
        "argmax": mp.nstr(maximum_x, 18),
    }


# ---------------------------------------------------------------------------
# Exact cardinal obstructions and endpoint derivative defects
# ---------------------------------------------------------------------------


def cardinal_mode_components(N: int) -> tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    """Return A0,a,B0,b for the two exact lower-bound modes A0*a^(m+1), B0*b^(m+1)."""
    if N % 2:
        raise ValueError("N must be even")
    mp.mp.dps = max(80, N)
    A0 = mp.gamma(N - mp.mpf("0.5")) / (
        mp.sqrt(mp.pi)
        * (mp.mpf(N) / 2 - mp.mpf("0.5"))
        * mp.gamma(mp.mpf(N) / 2) ** 2
    )
    a = mp.mpf(2 * N - 1) / (N * N)
    B0 = mp.gamma(mp.mpf(N) / 2 - mp.mpf("0.5")) ** 2 / (
        mp.pi * mp.gamma(N - 1)
    )
    b = mp.mpf(N + 1) / 4
    return A0, a, B0, b


def cardinal_mode_bounds(N: int, m: int) -> tuple[mp.mpf, mp.mpf]:
    A0, a, B0, b = cardinal_mode_components(N)
    k = m + 1
    return A0 * a**k, B0 * b**k


def balanced_jet_order(N: int) -> mp.mpf:
    A0, a, B0, b = cardinal_mode_components(N)
    return mp.log(A0 / B0) / mp.log(b / a) - 1


def critical_jet_orders(N: int) -> tuple[mp.mpf, mp.mpf]:
    """Leading-order lower and upper boundary-mode thresholds."""
    n = mp.mpf(N)
    return n * mp.log(2) / mp.log(n / 2), n * mp.log(2) / mp.log(n / 4)


def endpoint_derivative_defect(N: int) -> Fraction:
    """Exact P_N'(0) for the ordinary Fabius Lagrange interpolant."""
    if N <= 1 or N & (N - 1):
        raise ValueError("N must be a power of two")
    exponent = N.bit_length() - 1
    total = Fraction(0)
    for j in range(1, N + 1):
        total += (
            Fraction((-1) ** (j + 1) * math.comb(N, j), j)
            * FABIUS.value(exponent, j)
        )
    return N * total


# ---------------------------------------------------------------------------
# CSV helpers and task implementations
# ---------------------------------------------------------------------------


def write_rows(path: Path, rows: Sequence[dict[str, object]]) -> None:
    if not rows:
        raise ValueError("refusing to write an empty CSV")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def parse_int_list(text: str) -> list[int]:
    return [int(part.strip()) for part in text.split(",") if part.strip()]


def task_endpoint(args: argparse.Namespace, target: str) -> None:
    rows: list[dict[str, object]] = []
    for m in range(args.m_start, args.m_end + 1):
        start = time.perf_counter()
        dps = args.dps or precision_for(args.N, m)
        interpolant = build_endpoint_flat_interpolant(target, args.N, m, dps)
        row = scan_error(interpolant, target, args.N, m, args.grid_level)
        rows.append(row)
        print(
            f"{target:7s} N={args.N:4d} m={m:3d} "
            f"error={row['max_abs_error']} x={row['argmax']} "
            f"({time.perf_counter()-start:.2f}s)",
            flush=True,
        )
    output = Path(args.output) if args.output else Path(f"{target}_N{args.N}.csv")
    write_rows(output, rows)


def task_hermite(args: argparse.Namespace) -> None:
    rows = []
    for N in parse_int_list(args.N_list):
        start = time.perf_counter()
        row = scan_first_hermite(N, args.grid_level)
        rows.append(row)
        print(
            f"all-node Hermite N={N:4d} error={row['max_abs_error']} "
            f"({time.perf_counter()-start:.2f}s)",
            flush=True,
        )
    write_rows(Path(args.output or "hermite_first_derivative.csv"), rows)


def task_derivative(args: argparse.Namespace) -> None:
    rows: list[dict[str, object]] = []
    for n in range(args.n_min, args.n_max + 1):
        N = 1 << n
        start = time.perf_counter()
        defect = endpoint_derivative_defect(N)
        value = mp_from_fraction(defect)
        rows.append(
            {
                "n": n,
                "N": N,
                "sign": 1 if defect > 0 else -1 if defect < 0 else 0,
                "log2_abs_derivative": mp.nstr(mp.log(abs(value), 2), 28),
                "binary_deficit": mp.nstr(N - mp.log(abs(value), 2), 28),
                "numerator_digits_estimate": int((abs(defect.numerator).bit_length() - 1) * math.log10(2)) + 1,
                "denominator_digits_estimate": int((defect.denominator.bit_length() - 1) * math.log10(2)) + 1,
            }
        )
        print(
            f"N={N:6d} log2|P'(0)|={rows[-1]['log2_abs_derivative']} "
            f"({time.perf_counter()-start:.2f}s)",
            flush=True,
        )
    write_rows(Path(args.output or "endpoint_derivative_defects.csv"), rows)


def task_predictions(args: argparse.Namespace) -> None:
    rows: list[dict[str, object]] = []
    for N in parse_int_list(args.N_list):
        m_bal = balanced_jet_order(N)
        lower, upper = critical_jet_orders(N)
        A0, a, B0, b = cardinal_mode_components(N)
        A_bal = A0 * a ** (m_bal + 1)
        rows.append(
            {
                "N": N,
                "m_balance": mp.nstr(m_bal, 28),
                "m_lower_asymptotic": mp.nstr(lower, 28),
                "m_upper_asymptotic": mp.nstr(upper, 28),
                "A0": mp.nstr(A0, 28),
                "a": mp.nstr(a, 28),
                "B0": mp.nstr(B0, 28),
                "b": mp.nstr(b, 28),
                "balanced_mode_bound": mp.nstr(A_bal, 28),
            }
        )
        print(f"N={N:4d} m_balance={mp.nstr(m_bal, 12)}", flush=True)
    write_rows(Path(args.output or "jet_order_predictions.csv"), rows)


def task_lebesgue(args: argparse.Namespace) -> None:
    rows = []
    for m in range(args.m_start, args.m_end + 1):
        start = time.perf_counter()
        row = weighted_lebesgue_maximum(args.N, m, args.grid_level)
        A, B = cardinal_mode_bounds(args.N, m)
        row["boundary_to_center_bound"] = mp.nstr(A, 28)
        row["center_to_boundary_bound"] = mp.nstr(B, 28)
        rows.append(row)
        print(
            f"Lebesgue N={args.N:4d} m={m:3d} max={row['max_weighted_lebesgue']} "
            f"({time.perf_counter()-start:.2f}s)",
            flush=True,
        )
    write_rows(Path(args.output or f"lebesgue_N{args.N}.csv"), rows)


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream))


def task_figures(args: argparse.Namespace) -> None:
    import matplotlib.pyplot as plt

    data_dir = Path(args.data_dir)
    figure_dir = Path(args.figure_dir)
    figure_dir.mkdir(parents=True, exist_ok=True)

    fabius = read_csv(data_dir / "fabius_endpoint_flat.csv")
    up = read_csv(data_dir / "up_endpoint_flat.csv")
    hermite = read_csv(data_dir / "hermite_first_derivative.csv")
    predictions = read_csv(data_dir / "jet_order_predictions.csv")
    lebesgue = read_csv(data_dir / "lebesgue_N64.csv")
    derivative = read_csv(data_dir / "endpoint_derivative_defects.csv")

    def group(rows: list[dict[str, str]], key: str) -> dict[int, list[dict[str, str]]]:
        result: dict[int, list[dict[str, str]]] = {}
        for row in rows:
            result.setdefault(int(row[key]), []).append(row)
        for values in result.values():
            values.sort(key=lambda r: int(r.get("m", 0)))
        return result

    # Figure 1: error versus endpoint jet order for F.
    plt.figure(figsize=(7.2, 4.6))
    for N, rows in sorted(group(fabius, "N").items()):
        plt.semilogy(
            [int(r["m"]) for r in rows],
            [float(r["max_abs_error"]) for r in rows],
            marker="o",
            markersize=3,
            label=f"N={N}",
        )
    plt.xlabel("endpoint jet order m")
    plt.ylabel("sampled max absolute error")
    plt.title("Fabius interpolation: a narrow finite-N stabilization window")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "fabius_error_vs_jet.pdf")
    plt.close()

    # Figure 2: same for the centered Rvachev bump.
    plt.figure(figsize=(7.2, 4.6))
    for N, rows in sorted(group(up, "N").items()):
        plt.semilogy(
            [int(r["m"]) for r in rows],
            [float(r["max_abs_error"]) for r in rows],
            marker="o",
            markersize=3,
            label=f"N={N}",
        )
    plt.xlabel("endpoint jet order m")
    plt.ylabel("sampled max absolute error")
    plt.title("Rvachev bump interpolation: suppression and reverse blow-up")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "up_error_vs_jet.pdf")
    plt.close()

    # Figure 3: ordinary Lagrange, best endpoint-flat result, and all-node Hermite.
    fgroup = group(fabius, "N")
    hmap = {int(r["N"]): r for r in hermite}
    common = sorted(set(fgroup) & set(hmap))
    ordinary = []
    best = []
    all_node = []
    for N in common:
        rows = fgroup[N]
        ordinary.append(float(next(r for r in rows if int(r["m"]) == 0)["max_abs_error"]))
        best.append(min(float(r["max_abs_error"]) for r in rows))
        all_node.append(float(hmap[N]["max_abs_error"]))
    plt.figure(figsize=(7.2, 4.6))
    plt.semilogy(common, ordinary, marker="o", label="ordinary Lagrange")
    plt.semilogy(common, best, marker="o", label="best tested endpoint-flat jet")
    plt.semilogy(common, all_node, marker="o", label="first derivative at every node")
    plt.xlabel("N (number of dyadic subintervals)")
    plt.ylabel("sampled max absolute error")
    plt.title("Higher derivatives help only when imposed selectively")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "method_comparison.pdf")
    plt.close()

    # Figure 4: actual weighted Lebesgue maximum and the two exact lower modes.
    plt.figure(figsize=(7.2, 4.6))
    m_values = [int(r["m"]) for r in lebesgue]
    plt.semilogy(
        m_values,
        [float(r["max_weighted_lebesgue"]) for r in lebesgue],
        marker="o",
        markersize=3,
        label="sampled weighted Lebesgue maximum",
    )
    plt.semilogy(
        m_values,
        [float(r["boundary_to_center_bound"]) for r in lebesgue],
        label="boundary-to-center cardinal mode",
    )
    plt.semilogy(
        m_values,
        [float(r["center_to_boundary_bound"]) for r in lebesgue],
        label="center-to-boundary cardinal mode",
    )
    pred64 = next(r for r in predictions if int(r["N"]) == 64)
    plt.axvline(float(pred64["m_balance"]), linestyle="--", label="two-mode balance")
    plt.xlabel("endpoint jet order m")
    plt.ylabel("amplification factor")
    plt.title("Conditioning at N=64: two opposing endpoint modes")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "conditioning_window_N64.pdf")
    plt.close()

    # Figure 5: exact endpoint derivative defect.
    plt.figure(figsize=(7.2, 4.6))
    n_values = [int(r["n"]) for r in derivative]
    plt.plot(n_values, [float(r["binary_deficit"]) for r in derivative], marker="o")
    plt.xlabel("n, where N=2^n")
    plt.ylabel("N - log2 |P_N'(0)|")
    plt.title("Exact endpoint derivative defect: evidence for a quadratic-log deficit")
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(figure_dir / "endpoint_derivative_deficit.pdf")
    plt.close()

    # Figure 6: detailed F error profiles at N=64.
    N = 64
    profile_m = [0, 14, 24]
    grid_level = 11
    denominator = 1 << grid_level
    x_values = [a / denominator for a in range(denominator + 1)]
    plt.figure(figsize=(7.2, 4.6))
    for m in profile_m:
        interp = build_endpoint_flat_interpolant("fabius", N, m, precision_for(N, m))
        errors = []
        for a in range(denominator + 1):
            x = mp.mpf(a) / denominator
            err = abs(interp(x) - mp_from_fraction(FABIUS.value(grid_level, a)))
            errors.append(max(float(err), 1e-30))
        plt.semilogy(x_values, errors, label=f"m={m}")
    plt.xlabel("x")
    plt.ylabel("absolute error")
    plt.title("Fabius error profile at N=64")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "fabius_error_profile_N64.pdf")
    plt.close()

    print(f"wrote figures to {figure_dir}")


def task_smoke() -> None:
    assert FABIUS.value(2, 1) == Fraction(5, 72)
    assert FABIUS.value(3, 3) == Fraction(73, 288)
    for exponent in range(1, 8):
        denominator = 1 << exponent
        for numerator in range(denominator + 1):
            assert (
                FABIUS.value(exponent, numerator)
                + FABIUS.value(exponent, denominator - numerator)
                == 1
            )
    for m in range(6):
        assert beta_smoothstep_fraction(m, Fraction(0)) == 0
        assert beta_smoothstep_fraction(m, Fraction(1)) == 1
    ordinary = build_endpoint_flat_interpolant("fabius", 8, 0, 100)
    for j in range(9):
        x = mp.mpf(j) / 8
        assert abs(ordinary(x) - mp_from_fraction(FABIUS.value(3, j))) < mp.mpf("1e-80")
    print("smoke tests passed")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--task",
        required=True,
        choices=["smoke", "fabius", "up", "hermite", "derivative", "predictions", "lebesgue", "figures"],
    )
    parser.add_argument("--N", type=int, default=64)
    parser.add_argument("--N-list", default="8,16,32,64,128,256")
    parser.add_argument("--m-start", type=int, default=0)
    parser.add_argument("--m-end", type=int, default=18)
    parser.add_argument("--grid-level", type=int, default=12)
    parser.add_argument("--dps", type=int)
    parser.add_argument("--n-min", type=int, default=4)
    parser.add_argument("--n-max", type=int, default=14)
    parser.add_argument("--output")
    parser.add_argument("--data-dir", default="data")
    parser.add_argument("--figure-dir", default="figures")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.task == "smoke":
        task_smoke()
    elif args.task == "fabius":
        task_endpoint(args, "fabius")
    elif args.task == "up":
        task_endpoint(args, "up")
    elif args.task == "hermite":
        task_hermite(args)
    elif args.task == "derivative":
        task_derivative(args)
    elif args.task == "predictions":
        task_predictions(args)
    elif args.task == "lebesgue":
        task_lebesgue(args)
    elif args.task == "figures":
        task_figures(args)
    else:  # pragma: no cover
        raise AssertionError(args.task)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
