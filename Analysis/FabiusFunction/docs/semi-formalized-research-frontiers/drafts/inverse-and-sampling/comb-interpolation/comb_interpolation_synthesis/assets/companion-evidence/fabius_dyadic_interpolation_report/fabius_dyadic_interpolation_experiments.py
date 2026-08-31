#!/usr/bin/env python3
"""High-precision experiments for dyadic interpolation of Fabius/Rvachev functions.

This program accompanies the report

    Dyadic-Comb Interpolation of the Fabius and Rvachev Functions

It deliberately separates three numerical layers:

1. Exact arithmetic at every dyadic sample.  The Fabius values are generated as
   fractions from the Thue--Morse/half-moment formula, using a streaming prefix
   recurrence.  No floating-point approximation enters the input data.
2. High-precision barycentric evaluation of the endpoint-flat global Hermite
   interpolants.  The precision is increased with the polynomial degree because
   the equispaced value-data operator is exponentially ill-conditioned.
3. Independent comparison on a finer dyadic grid, whose reference values are
   again exact fractions before conversion to ``mpmath`` numbers.

The default ``quick`` mode is intended as a smoke test.  ``--mode report``
recreates the CSV tables and figures shipped in the archive; it is intentionally
more expensive.  The code uses only standard Python, mpmath, NumPy, and
Matplotlib.  It does not rely on SciPy's floating-point polynomial routines,
which would hide the conditioning phenomena being studied.

Examples
--------
    python fabius_dyadic_interpolation_experiments.py --mode quick
    python fabius_dyadic_interpolation_experiments.py --mode report \
        --output-dir reproduced-results

The reported errors are sampled sup norms on the indicated fine dyadic grid,
not interval-certified continuous sup norms.  Increasing ``--check-level`` is a
simple resolution check; the exact input arithmetic is unchanged.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Callable, Iterable, Sequence

import mpmath as mp
import numpy as np

# Use a noninteractive backend so the script works on servers and in CI.
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


# ---------------------------------------------------------------------------
# Exact dyadic arithmetic
# ---------------------------------------------------------------------------


def thue_morse_sign(k: int) -> int:
    """Return (-1)^{s_2(k)}, where s_2 is the binary digit sum."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    return -1 if k.bit_count() & 1 else 1


@lru_cache(maxsize=None)
def half_moments(max_order: int) -> tuple[Fraction, ...]:
    r"""Return the exact half moments d_0,...,d_max_order.

    They satisfy

        (n+1)(2^n-1)d_n = sum_{k=0}^{n-1} binom(n+1,k)d_k,

    equivalently

        d_n = 1/(2^n-1) * sum_{j=1}^n binom(n,j)d_{n-j}/(j+1).

    The recurrence is triangular and therefore exact over ``Fraction``.
    """
    if max_order < 0:
        raise ValueError("max_order must be nonnegative")
    d: list[Fraction] = [Fraction(1)]
    for n in range(1, max_order + 1):
        total = Fraction(0)
        for j in range(1, n + 1):
            total += Fraction(math.comb(n, j), j + 1) * d[n - j]
        d.append(total / (2**n - 1))
    return tuple(d)


@lru_cache(maxsize=None)
def fabius_grid_exact(level: int) -> tuple[Fraction, ...]:
    r"""Return F(a/2^level), 0 <= a <= 2^level, exactly.

    We use the equivalent half-moment form of the repository's exact dyadic
    Thue--Morse formula:

      F(a/2^n) = 2^{-n(n-1)/2}/n! *
                 sum_{h=0}^{a-1} eps_h
                 sum_{j=0}^n binom(n,j)d_j(a-1-h)^{n-j}.

    To evaluate the entire comb in O(2^n n^2) rather than O(4^n), define

      S_k(a) = sum_{h=0}^{a-1} eps_h (a-1-h)^k.

    Then

      S_0(a+1) = S_0(a)+eps_a,
      S_k(a+1) = sum_{q=0}^k binom(k,q)S_q(a),  k >= 1.

    All S_k are integers, and the final values are exact fractions.
    """
    if level < 0:
        raise ValueError("level must be nonnegative")
    n = level
    count = 2**n
    d = half_moments(n)
    scale = Fraction(1, (2 ** (n * (n - 1) // 2)) * math.factorial(n))

    # S[k] stores S_k(a) at the current numerator a.
    S = [0] * (n + 1)
    values: list[Fraction] = []

    for a in range(count + 1):
        total = Fraction(0)
        for j in range(n + 1):
            total += math.comb(n, j) * d[j] * S[n - j]
        values.append(scale * total)

        if a == count:
            break

        eps = thue_morse_sign(a)
        new_S = [0] * (n + 1)
        new_S[0] = S[0] + eps
        for k in range(1, n + 1):
            new_S[k] = sum(math.comb(k, q) * S[q] for q in range(k + 1))
        S = new_S

    # Cheap exact sanity checks.  They catch indexing or 0^0 mistakes.
    assert values[0] == 0
    assert values[-1] == 1
    for a in range(count + 1):
        assert values[a] + values[count - a] == 1
    return tuple(values)


def fraction_to_mp(value: Fraction) -> mp.mpf:
    """Convert a Fraction without passing through binary double precision."""
    return mp.mpf(value.numerator) / value.denominator


def fabius_derivative_grid_exact(level: int) -> tuple[Fraction, ...]:
    r"""Return F'(a/2^level) exactly at all grid nodes.

    The identity F'(x)=2 up(2x-1) and up(t)=F(1-|t|) gives

       F'(a/2^n) = 2 F(a/2^{n-1})              for a <= 2^{n-1},
                 = 2 F((2^n-a)/2^{n-1})       for a >= 2^{n-1}.

    At level zero the two endpoint derivatives are zero by flatness.
    """
    if level < 0:
        raise ValueError("level must be nonnegative")
    if level == 0:
        return (Fraction(0), Fraction(0))
    n = 2**level
    half = n // 2
    coarse = fabius_grid_exact(level - 1)
    result = []
    for a in range(n + 1):
        idx = a if a <= half else n - a
        result.append(2 * coarse[idx])
    return tuple(result)


# ---------------------------------------------------------------------------
# Endpoint-flat global interpolation
# ---------------------------------------------------------------------------


def smoothstep(x: mp.mpf, r: int) -> mp.mpf:
    r"""The degree-(2r+1) endpoint-flat transition S_r.

      S_r(x) = I_x(r+1,r+1)
             = (2r+1)!/(r!)^2 * sum_{k=0}^r
               (-1)^k binom(r,k) x^{r+k+1}/(r+k+1).

    It has S_r(0)=0, S_r(1)=1, and derivatives 1,...,r equal to
    zero at both endpoints.  The polynomial formula is used instead of a
    special-function call so that the numerical object matches the report.
    """
    if r < 0:
        raise ValueError("r must be nonnegative")
    prefactor = mp.factorial(2 * r + 1) / (mp.factorial(r) ** 2)
    total = mp.mpf("0")
    for k in range(r + 1):
        total += ((-1) ** k) * math.comb(r, k) * x ** (r + k + 1) / (r + k + 1)
    return prefactor * total


def interior_barycentric_weights(N: int) -> tuple[int, ...]:
    r"""Scaled barycentric weights for x_j=j/N, j=1,...,N-1.

    A common nonzero factor is irrelevant, so the exact integer weights

        w_j = (-1)^{j-1} binom(N-2,j-1)

    are ideal for high-precision evaluation.
    """
    if N < 2:
        raise ValueError("N must be at least 2")
    return tuple(((-1) ** (j - 1)) * math.comb(N - 2, j - 1) for j in range(1, N))


def barycentric_interior(
    x: mp.mpf,
    N: int,
    values: Sequence[mp.mpf],
    weights: Sequence[int],
) -> mp.mpf:
    """Evaluate the interior-node interpolant in second barycentric form."""
    if len(values) != N - 1 or len(weights) != N - 1:
        raise ValueError("interior data must have length N-1")

    # Exact-node detection is important on the dyadic comparison grid.  Using
    # a very small tolerance also handles values created by decimal input.
    tol = mp.eps * 16
    for idx, j in enumerate(range(1, N)):
        node = mp.mpf(j) / N
        if abs(x - node) <= tol * max(mp.mpf(1), abs(node)):
            return values[idx]

    numerator = mp.mpf("0")
    denominator = mp.mpf("0")
    for idx, j in enumerate(range(1, N)):
        term = mp.mpf(weights[idx]) / (x - mp.mpf(j) / N)
        numerator += term * values[idx]
        denominator += term
    return numerator / denominator


@dataclass(frozen=True)
class EndpointFlatInterpolant:
    """Callable representation of the global endpoint-flat interpolant."""

    target: str
    N: int
    r: int
    transformed_values: tuple[mp.mpf, ...]
    weights: tuple[int, ...]

    def __call__(self, x: mp.mpf) -> mp.mpf:
        # Here x is in [0,1].  For target='up', it represents t=2x-1.
        if x == 0:
            return mp.mpf("0")
        if x == 1:
            return mp.mpf("1") if self.target == "fabius" else mp.mpf("0")

        D = (x * (1 - x)) ** (self.r + 1)
        residual = barycentric_interior(x, self.N, self.transformed_values, self.weights)
        if self.target == "fabius":
            return smoothstep(x, self.r) + D * residual
        if self.target == "up":
            return D * residual
        raise ValueError(f"unknown target {self.target!r}")


def make_endpoint_flat_interpolant(target: str, N: int, r: int) -> EndpointFlatInterpolant:
    """Construct H^F_{N,r} or the affine version of H^up_{N,r}."""
    if target not in {"fabius", "up"}:
        raise ValueError("target must be 'fabius' or 'up'")
    if N < 2 or N & (N - 1):
        raise ValueError("N must be a dyadic power at least 2")
    if r < 0:
        raise ValueError("r must be nonnegative")

    level = N.bit_length() - 1
    grid = fabius_grid_exact(level)
    transformed: list[mp.mpf] = []

    for j in range(1, N):
        x = mp.mpf(j) / N
        D = (x * (1 - x)) ** (r + 1)
        if target == "fabius":
            y = fraction_to_mp(grid[j])
            transformed.append((y - smoothstep(x, r)) / D)
        else:
            # up(2x-1)=F(1-|2x-1|).  The argument is a node of the
            # level-(log2 N - 1) grid; using the fine grid's even index is
            # equivalent and avoids a special case.
            arg_index = 2 * j if j <= N // 2 else 2 * (N - j)
            # arg_index/N = 1-|2x-1|.  Reduce by reading the level grid.
            y = fraction_to_mp(grid[arg_index] if arg_index <= N else grid[2 * N - arg_index])
            # The previous expression is unnecessarily defensive; for
            # 1<=j<=N-1, arg_index always lies in [2,N].
            transformed.append(y / D)

    return EndpointFlatInterpolant(
        target=target,
        N=N,
        r=r,
        transformed_values=tuple(transformed),
        weights=interior_barycentric_weights(N),
    )


def exact_reference(target: str, check_level: int) -> tuple[np.ndarray, tuple[Fraction, ...]]:
    """Return the affine x-grid and exact target values for error sampling."""
    M = 2**check_level
    xs = np.linspace(0.0, 1.0, M + 1)
    if target == "fabius":
        return xs, fabius_grid_exact(check_level)
    if target != "up":
        raise ValueError("unknown target")

    # On t=2x-1, up(t)=F(1-|t|).  For x=i/2^K the F argument has
    # denominator 2^(K-1).  Store the resulting exact values.
    if check_level == 0:
        return xs, (Fraction(0), Fraction(0))
    fine = fabius_grid_exact(check_level - 1)
    half = M // 2
    vals: list[Fraction] = []
    for i in range(M + 1):
        idx = i if i <= half else M - i
        vals.append(fine[idx])
    return xs, tuple(vals)


def sampled_error(
    interpolant: EndpointFlatInterpolant,
    check_level: int,
) -> tuple[mp.mpf, mp.mpf]:
    """Sample the maximum error and its affine x-location."""
    xs, exact = exact_reference(interpolant.target, check_level)
    max_error = mp.mpf("-1")
    argmax = mp.mpf("0")
    M = 2**check_level
    for i, ref_fraction in enumerate(exact):
        x = mp.mpf(i) / M
        approx = interpolant(x)
        ref = fraction_to_mp(ref_fraction)
        error = abs(approx - ref)
        if error > max_error:
            max_error = error
            argmax = x
    return max_error, argmax


def recommended_dps(N: int, r: int) -> int:
    """Conservative working precision for the unstable global problem."""
    return max(100, int(2.15 * N + 4 * r + 40))


def scan_errors(
    targets: Sequence[str],
    Ns: Sequence[int],
    rs: Sequence[int],
    check_level: int,
) -> list[dict[str, str | int]]:
    """Compute a rectangular table of sampled errors."""
    rows: list[dict[str, str | int]] = []
    for target in targets:
        for N in Ns:
            if N > 2**check_level:
                raise ValueError("comparison grid must be at least as fine as interpolation grid")
            for r in rs:
                dps = recommended_dps(N, r)
                with mp.workdps(dps):
                    interp = make_endpoint_flat_interpolant(target, N, r)
                    error, argmax = sampled_error(interp, check_level)
                rows.append(
                    {
                        "target": target,
                        "N": N,
                        "r": r,
                        "degree": N + 2 * r,
                        "check_level": check_level,
                        "dps": dps,
                        "sampled_max_error": mp.nstr(error, 18),
                        "argmax_affine_x": mp.nstr(argmax, 18),
                    }
                )
                print(
                    f"{target:6s} N={N:3d} r={r:2d} degree={N+2*r:3d} "
                    f"error={mp.nstr(error, 9)} at x={mp.nstr(argmax, 7)}"
                )
    return rows


# ---------------------------------------------------------------------------
# Piecewise cubic Hermite interpolation: a stable local comparison
# ---------------------------------------------------------------------------


def piecewise_cubic_fabius_value(x: mp.mpf, N: int) -> mp.mpf:
    """Evaluate the cellwise cubic Hermite interpolant to F on N dyadic cells."""
    if x <= 0:
        return mp.mpf("0")
    if x >= 1:
        return mp.mpf("1")
    level = N.bit_length() - 1
    values = fabius_grid_exact(level)
    derivatives = fabius_derivative_grid_exact(level)

    scaled = x * N
    j = min(int(mp.floor(scaled)), N - 1)
    u = scaled - j
    h = mp.mpf(1) / N
    f0 = fraction_to_mp(values[j])
    f1 = fraction_to_mp(values[j + 1])
    d0 = fraction_to_mp(derivatives[j])
    d1 = fraction_to_mp(derivatives[j + 1])

    h00 = 2 * u**3 - 3 * u**2 + 1
    h10 = u**3 - 2 * u**2 + u
    h01 = -2 * u**3 + 3 * u**2
    h11 = u**3 - u**2
    return h00 * f0 + h10 * h * d0 + h01 * f1 + h11 * h * d1


def piecewise_cubic_errors(Ns: Sequence[int], check_level: int) -> list[dict[str, str | int]]:
    xs, exact = exact_reference("fabius", check_level)
    M = 2**check_level
    rows: list[dict[str, str | int]] = []
    with mp.workdps(100):
        for N in Ns:
            max_error = mp.mpf("-1")
            argmax = mp.mpf("0")
            for i, ref_fraction in enumerate(exact):
                x = mp.mpf(i) / M
                error = abs(piecewise_cubic_fabius_value(x, N) - fraction_to_mp(ref_fraction))
                if error > max_error:
                    max_error = error
                    argmax = x
            rows.append(
                {
                    "target": "fabius_piecewise_cubic",
                    "N": N,
                    "degree": 3,
                    "check_level": check_level,
                    "sampled_max_error": mp.nstr(max_error, 18),
                    "argmax_affine_x": mp.nstr(argmax, 18),
                }
            )
            print(f"local cubic N={N:3d} error={mp.nstr(max_error, 9)}")
    return rows


# ---------------------------------------------------------------------------
# Exact cardinal-amplification formulas used in the report
# ---------------------------------------------------------------------------


def cardinal_mode_half_cell(N: int, r: int) -> mp.mpf:
    r"""Central cardinal at x=1/(2N), the fixed-r boundary-layer mode."""
    return (
        (mp.mpf(2) / N * (1 - mp.mpf(1) / (2 * N))) ** (r + 1)
        * mp.gamma(N - mp.mpf("0.5"))
        / (mp.sqrt(mp.pi) * (mp.mpf(N) / 2 - mp.mpf("0.5")) * mp.gamma(mp.mpf(N) / 2) ** 2)
    )


def cardinal_mode_one_third(N: int, r: int) -> mp.mpf:
    r"""Central cardinal at x=1/3; N must not be divisible by three."""
    if N % 3 == 0:
        raise ValueError("x=1/3 is a node when 3 divides N")
    return (
        (mp.mpf(8) / 9) ** (r + 1)
        * (3 * mp.sqrt(3) / (mp.pi * N))
        * mp.gamma(mp.mpf(N) / 3)
        * mp.gamma(2 * mp.mpf(N) / 3)
        / mp.gamma(mp.mpf(N) / 2) ** 2
    )


def cardinal_mode_near_center(N: int, r: int) -> mp.mpf:
    r"""Boundary-node cardinal at x=1/2+1/(2N)."""
    return (
        (mp.mpf(N + 1) / 4) ** (r + 1)
        * mp.gamma(mp.mpf(N) / 2 - mp.mpf("0.5")) ** 2
        / (mp.pi * mp.gamma(N - 1))
    )


def balancing_order(N: int) -> float:
    r"""Asymptotic jet order obtained by balancing two boundary modes.

        r_bal(N) = 2 N log 2 / (2 log N - 3 log 2).

    This is not a stability theorem; it predicts the numerically favorable
    window observed for the particular Fabius/Rvachev data.
    """
    return 2 * N * math.log(2) / (2 * math.log(N) - 3 * math.log(2))


# ---------------------------------------------------------------------------
# Output helpers and figures
# ---------------------------------------------------------------------------


def write_csv(path: Path, rows: Sequence[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    fieldnames: list[str] = []
    for row in rows:
        for key in row:
            if key not in fieldnames:
                fieldnames.append(key)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def _save_figure(fig: plt.Figure, stem: Path) -> None:
    stem.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(stem.with_suffix(".pdf"), bbox_inches="tight")
    fig.savefig(stem.with_suffix(".png"), dpi=180, bbox_inches="tight")
    plt.close(fig)


def plot_interpolants(target: str, N: int, rs: Sequence[int], out_stem: Path) -> None:
    """Plot the target and selected global interpolants."""
    plot_level = 10
    xs_np, exact = exact_reference(target, plot_level)
    ys_ref = np.array([float(v) for v in exact])

    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    horizontal = xs_np if target == "fabius" else 2 * xs_np - 1
    ax.plot(horizontal, ys_ref, linewidth=2.2, label="exact dyadic reference")

    for r in rs:
        with mp.workdps(recommended_dps(N, r)):
            interp = make_endpoint_flat_interpolant(target, N, r)
            vals = np.array([float(interp(mp.mpf(i) / (2**plot_level))) for i in range(2**plot_level + 1)])
        ax.plot(horizontal, vals, linewidth=1.1, label=f"r={r}, degree={N+2*r}")

    ax.set_xlabel("x" if target == "fabius" else "t")
    ax.set_ylabel("F(x)" if target == "fabius" else "up(t)")
    ax.set_title(
        f"Endpoint-flat global interpolation: {'Fabius F' if target == 'fabius' else 'Rvachev up'}, N={N}"
    )
    ax.grid(True, alpha=0.25)
    ax.legend(loc="best", fontsize=8)
    _save_figure(fig, out_stem)


def plot_jet_scan(rows: Sequence[dict[str, object]], out_stem: Path) -> None:
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for target in ("fabius", "up"):
        selected = [row for row in rows if row["target"] == target]
        selected.sort(key=lambda row: int(row["r"]))
        ax.semilogy(
            [int(row["r"]) for row in selected],
            [float(row["sampled_max_error"]) for row in selected],
            marker="o",
            markersize=3,
            linewidth=1.2,
            label="Fabius F" if target == "fabius" else "Rvachev up",
        )
    ax.set_xlabel("endpoint jet order r")
    ax.set_ylabel("sampled maximum error")
    ax.set_title("U-shaped error window on the N=64 dyadic comb")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(loc="best")
    _save_figure(fig, out_stem)


def plot_balance(rows: Sequence[dict[str, object]], out_stem: Path) -> None:
    """Compare observed minimizing r with the two-mode balancing law."""
    Ns = sorted({int(row["N"]) for row in rows})
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for target in ("fabius", "up"):
        observed = []
        for N in Ns:
            subset = [row for row in rows if row["target"] == target and int(row["N"]) == N]
            if not subset:
                observed.append(np.nan)
            else:
                best = min(subset, key=lambda row: float(row["sampled_max_error"]))
                observed.append(int(best["r"]))
        ax.plot(Ns, observed, marker="o", linewidth=1.2, label=f"observed: {target}")
    ax.plot(Ns, [balancing_order(N) for N in Ns], marker="s", linestyle="--", label="two-mode balance")
    ax.set_xlabel("N")
    ax.set_ylabel("jet order")
    ax.set_title("Observed favorable jet order and the balancing prediction")
    ax.grid(True, alpha=0.25)
    ax.legend(loc="best")
    _save_figure(fig, out_stem)


def plot_global_vs_local(
    global_rows: Sequence[dict[str, object]],
    local_rows: Sequence[dict[str, object]],
    out_stem: Path,
) -> None:
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    ordinary = [row for row in global_rows if row["target"] == "fabius" and int(row["r"]) == 0]
    ordinary.sort(key=lambda row: int(row["N"]))
    local = sorted(local_rows, key=lambda row: int(row["N"]))
    ax.semilogy(
        [int(row["N"]) for row in ordinary],
        [float(row["sampled_max_error"]) for row in ordinary],
        marker="o",
        linewidth=1.2,
        label="global ordinary Lagrange",
    )
    ax.semilogy(
        [int(row["N"]) for row in local],
        [float(row["sampled_max_error"]) for row in local],
        marker="s",
        linewidth=1.2,
        label="piecewise cubic Hermite",
    )
    ax.set_xlabel("number N of dyadic cells")
    ax.set_ylabel("sampled maximum error")
    ax.set_title("Global Runge growth versus stable local interpolation")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(loc="best")
    _save_figure(fig, out_stem)


def make_cardinal_table(Ns: Sequence[int], out_path: Path) -> None:
    rows: list[dict[str, object]] = []
    with mp.workdps(100):
        for N in Ns:
            rb = balancing_order(N)
            r = int(round(rb))
            rows.append(
                {
                    "N": N,
                    "r_balance": f"{rb:.12g}",
                    "rounded_r": r,
                    "half_cell_mode": mp.nstr(cardinal_mode_half_cell(N, r), 18),
                    "one_third_mode": mp.nstr(cardinal_mode_one_third(N, r), 18),
                    "near_center_mode": mp.nstr(cardinal_mode_near_center(N, r), 18),
                }
            )
    write_csv(out_path, rows)


def run_quick(output_dir: Path, check_level: int) -> None:
    fixed = scan_errors(
        targets=("fabius", "up"),
        Ns=(8, 16, 32),
        rs=(0, 2, 4, 8),
        check_level=check_level,
    )
    local = piecewise_cubic_errors((4, 8, 16, 32), check_level)
    write_csv(output_dir / "data" / "quick_global_errors.csv", fixed)
    write_csv(output_dir / "data" / "quick_piecewise_cubic_errors.csv", local)
    plot_interpolants("fabius", 32, (0, 4, 8), output_dir / "figures" / "fabius_N32_interpolants")
    plot_interpolants("up", 32, (0, 4, 8), output_dir / "figures" / "up_N32_interpolants")
    plot_global_vs_local(fixed, local, output_dir / "figures" / "global_vs_local")
    make_cardinal_table((16, 32, 64), output_dir / "data" / "cardinal_modes.csv")


def run_report(output_dir: Path, check_level: int) -> None:
    fixed = scan_errors(
        targets=("fabius", "up"),
        Ns=(8, 16, 32, 64),
        rs=(0, 1, 2, 4, 8),
        check_level=check_level,
    )

    scan64 = scan_errors(
        targets=("fabius", "up"),
        Ns=(64,),
        rs=tuple(range(0, 21)),
        check_level=check_level,
    )

    # A focused N=128 window tests the balance prediction without doing an
    # unnecessarily broad and expensive scan.
    scan128 = scan_errors(
        targets=("fabius", "up"),
        Ns=(128,),
        rs=tuple(range(18, 29)),
        check_level=check_level,
    )

    balance_rows = []
    for N, scan in ((32, [row for row in fixed if int(row["N"]) == 32]), (64, scan64), (128, scan128)):
        for target in ("fabius", "up"):
            subset = [row for row in scan if row["target"] == target]
            if subset:
                balance_rows.extend(subset)

    local = piecewise_cubic_errors((4, 8, 16, 32, 64), check_level)

    write_csv(output_dir / "data" / "fixed_order_errors.csv", fixed)
    write_csv(output_dir / "data" / "jet_scan_N64.csv", scan64)
    write_csv(output_dir / "data" / "jet_scan_N128_window.csv", scan128)
    write_csv(output_dir / "data" / "piecewise_cubic_errors.csv", local)
    make_cardinal_table((16, 32, 64, 128, 256), output_dir / "data" / "cardinal_modes.csv")

    plot_interpolants("fabius", 32, (0, 4, 8), output_dir / "figures" / "fabius_N32_interpolants")
    plot_interpolants("up", 32, (0, 4, 8), output_dir / "figures" / "up_N32_interpolants")
    plot_jet_scan(scan64, output_dir / "figures" / "jet_order_scan_N64")
    plot_balance(balance_rows, output_dir / "figures" / "balancing_law")
    plot_global_vs_local(fixed, local, output_dir / "figures" / "global_vs_local")


# ---------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mode",
        choices=("quick", "report"),
        default="quick",
        help="quick smoke test or the more expensive report reproduction",
    )
    parser.add_argument(
        "--check-level",
        type=int,
        default=11,
        help="sample errors on 2^K equal subintervals (default: 11)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("interpolation-results"),
        help="directory for CSV files and figures",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.check_level < 8:
        raise SystemExit("use --check-level at least 8 for meaningful comparisons")
    args.output_dir.mkdir(parents=True, exist_ok=True)

    # Exact arithmetic self-checks before the expensive runs.
    assert fabius_grid_exact(1) == (Fraction(0), Fraction(1, 2), Fraction(1))
    assert fabius_grid_exact(2)[1] == Fraction(5, 72)
    assert fabius_grid_exact(2)[2] == Fraction(1, 2)

    if args.mode == "quick":
        run_quick(args.output_dir, args.check_level)
    else:
        run_report(args.output_dir, args.check_level)

    print(f"Results written under: {args.output_dir.resolve()}")


if __name__ == "__main__":
    main()
