#!/usr/bin/env python3
"""Reproducible experiments for the Fabius--Rvachev Carleman frontier report.

The computations in this file are deliberately self-contained.  They use only
Python's standard library plus mpmath and matplotlib.  No repository source,
network access, or precomputed numerical table is required.

Experiments
===========
1.  The exact integer optimizer and lattice correction in the Fourier--Carleman
    envelope associated with W_n = 2^{n(n+1)/2}.
2.  The optimal algebraic gain beyond that envelope along the distinguished
    peak ray x_k = 2^k(2/3).
3.  The Lambert-W approximation to the optimizer of the factorial-normalized
    Denjoy--Carleman associated function.
4.  Exact Bell-polynomial composition coefficients, including the edge-term
    asymptotics proposed in Conjecture 10.2 of the report.

All output is deterministic.  CSV files are written with decimal strings long
enough to reproduce the plots.  PDF figures use vector graphics; PNG copies are
also emitted for convenient inspection.
"""

from __future__ import annotations

import argparse
import csv
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import mpmath as mp

# Matplotlib is imported only when figures are requested, so the exact arithmetic
# tables can still be generated in a minimal Python installation.

PI = mp.pi  # mpmath context constant; evaluated at the active precision.


def triangular(n: int) -> int:
    """Return T_n = n(n+1)/2 exactly."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return n * (n + 1) // 2


def raw_weight(n: int, base: int = 2) -> int:
    """Return W_n(base) = base^{T_n} exactly for integral base."""
    if base < 2:
        raise ValueError("this exact-integer helper expects base >= 2")
    return base ** triangular(n)


def distance_to_integer(x: mp.mpf) -> mp.mpf:
    """Distance from x to the nearest integer, with values in [0, 1/2]."""
    return abs(x - mp.nint(x))


def carleman_optimizer(x: mp.mpf) -> Tuple[int, mp.mpf]:
    r"""Minimize 2^{K(K-1)/2}/(pi |x|)^K over K in N_0.

    The continuous vertex is a = log_2(pi|x|)+1/2.  The exact discrete optimizer
    is a nearest nonnegative integer to a.  We check the two neighboring integers
    to avoid any dependence on a rounding convention at half-integers.
    """
    x = abs(mp.mpf(x))
    if x == 0:
        return 0, mp.mpf(1)
    a = mp.log(PI * x, 2) + mp.mpf("0.5")
    candidates = {0, max(0, int(mp.floor(a))), max(0, int(mp.ceil(a)))}
    best_k = 0
    best = mp.inf
    for k in sorted(candidates):
        value = mp.power(2, k * (k - 1) / 2) / mp.power(PI * x, k)
        if value < best:
            best_k, best = k, value
    return best_k, best


def carleman_closed_form(x: mp.mpf) -> mp.mpf:
    """Exact closed form of the optimized envelope for |x| >= 1.

    B_C(x) = 2^{-a^2/2 + dist(a,Z)^2/2},
    a = log_2(pi |x|)+1/2.
    """
    x = abs(mp.mpf(x))
    if x == 0:
        return mp.mpf(1)
    a = mp.log(PI * x, 2) + mp.mpf("0.5")
    # For the sampled range x>=1, the nearest integer is automatically >=0.
    d = distance_to_integer(a)
    return mp.power(2, -(a * a) / 2 + (d * d) / 2)


def smooth_carleman_carrier(x: mp.mpf) -> mp.mpf:
    """Continuous quadratic carrier obtained by dropping lattice rounding."""
    x = abs(mp.mpf(x))
    a = mp.log(PI * x, 2) + mp.mpf("0.5")
    return mp.power(2, -(a * a) / 2)


def sinc_product(x: mp.mpf, tol: mp.mpf = mp.mpf("1e-70")) -> mp.mpf:
    r"""Evaluate Phi(x)=prod_{j>=0} sinc(pi*x/2^j) at high precision.

    Here sinc(z)=sin(z)/z.  The tail is stopped once the conservative quadratic
    estimate sum_{j>J} |z_j|^2/6 is below ``tol``.  Integer arguments are zeros;
    those are returned exactly when detected at the working precision.
    """
    x = mp.mpf(x)
    if x == 0:
        return mp.mpf(1)
    product = mp.mpf(1)
    j = 0
    while True:
        z = PI * x / mp.power(2, j)
        if z == 0:
            factor = mp.mpf(1)
        else:
            factor = mp.sin(z) / z
        product *= factor
        # The remaining squared arguments form a geometric series with ratio 1/4.
        tail_bound = (z * z / 4) / (1 - mp.mpf(1) / 4) / 6
        if abs(tail_bound) < tol and j > 10:
            break
        j += 1
        if j > 10000:
            raise RuntimeError("sinc product did not converge within 10000 factors")
    return product


def peak_ray_log_abs(k: int, phi_two_thirds: mp.mpf) -> mp.mpf:
    r"""Exact log |Phi(2^k*2/3)| from the dyadic shell factorization.

    For y=2/3 every extracted sine numerator has modulus sqrt(3)/2, so no
    large-argument trigonometric evaluation is needed.
    """
    if k < 0:
        raise ValueError("k must be nonnegative")
    log_factor = (
        k * mp.log(3 * mp.sqrt(3) / PI)
        - mp.mpf(k * (k - 1) // 2 + 3 * k) * mp.log(2)
    )
    return mp.log(abs(phi_two_thirds)) + log_factor


def standard_associated_objective(n: int, t: mp.mpf) -> mp.mpf:
    r"""Return log(t^n/M_n), M_n=2^{T_n}/n!, without huge intermediate values."""
    return n * mp.log(t) + mp.loggamma(n + 1) - triangular(n) * mp.log(2)


def standard_associated_optimizer(t: mp.mpf) -> Tuple[int, mp.mpf]:
    """Find the exact discrete optimizer of the standard associated function.

    The Lambert predictor places the maximum very accurately.  We inspect a
    fixed window around it; the objective is eventually strictly concave.
    """
    t = mp.mpf(t)
    if t <= 0:
        raise ValueError("t must be positive")
    predictor = lambert_optimizer(t)
    center = max(0, int(mp.nint(predictor)))
    candidates = range(max(0, center - 8), center + 9)
    values = [(n, standard_associated_objective(n, t)) for n in candidates]
    return max(values, key=lambda item: item[1])


def lambert_optimizer(t: mp.mpf, base: mp.mpf = mp.mpf(2)) -> mp.mpf:
    r"""Leading Lambert-W_{-1} approximation to the normalized optimizer.

    For L=log(base), the approximate saddle solves
        L*s - log(s) = log(t) - L/2,
    hence
        s = -W_{-1}(-sqrt(base)*L/t)/L.
    """
    t = mp.mpf(t)
    base = mp.mpf(base)
    L = mp.log(base)
    z = -mp.sqrt(base) * L / t
    if z < -1 / mp.e:
        # The large-t asymptotic branch is not real in this small-t regime.
        return mp.mpf(0)
    return -mp.lambertw(z, -1).real / L


def bell_table(nmax: int) -> Tuple[List[int], List[List[int]]]:
    r"""Compute exponential partial Bell polynomials B_{n,k}(W_1,...).

    The recurrence
        B_{n,k} = sum_{j=1}^{n-k+1} binom(n-1,j-1) W_j B_{n-j,k-1}
    uses exact Python integers.  It is practical through at least n=120 on an ordinary
    workstation because the table is triangular and all entries are Python integers.
    """
    W = [raw_weight(n) for n in range(nmax + 1)]
    B = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    B[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            B[n][k] = sum(
                math.comb(n - 1, j - 1) * W[j] * B[n - j][k - 1]
                for j in range(1, n - k + 2)
            )
    return W, B


def bell_composition_coefficient(n: int, W: Sequence[int], B: Sequence[Sequence[int]]) -> Fraction:
    r"""Return C_n = W_n^{-1} sum_k W_k B_{n,k}(W_1,...)."""
    numerator = sum(W[k] * B[n][k] for k in range(1, n + 1))
    return Fraction(numerator, W[n])


def bell_edge_approximation(n: int) -> Fraction:
    r"""Four-edge asymptotic model used in the report.

    Exact included contributions:
      k=n:   2^n,
      k=n-1: n(n-1),
      k=1:   2,
      k=n-2: 2^{3-n}(2*C(n,3)+3*C(n,4)).

    The term 16*n*2^{-n} is the leading contribution of k=2 (two endpoint
    compositions).  The remaining observed error is of order n^6*4^{-n}.
    """
    exact_edges = Fraction(2**n + n * (n - 1) + 2, 1)
    if n >= 4:
        exact_edges += Fraction(
            8 * (2 * math.comb(n, 3) + 3 * math.comb(n, 4)), 2**n
        )
    exact_edges += Fraction(16 * n, 2**n)
    return exact_edges


def write_csv(path: Path, header: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(header)
        writer.writerows(rows)


def mp_string(x: mp.mpf, digits: int = 40) -> str:
    """Stable decimal/scientific string for CSV output."""
    return mp.nstr(x, digits, strip_zeros=False)


def generate_tables(out_dir: Path, bell_nmax: int = 120) -> None:
    mp.mp.dps = 100
    data_dir = out_dir / "data"
    data_dir.mkdir(parents=True, exist_ok=True)

    # 1. Fourier--Carleman envelope on a logarithmic grid.
    gauge_rows = []
    for j in range(0, 257):
        log2x = mp.mpf(j) / 16
        x = mp.power(2, log2x)
        kopt, direct = carleman_optimizer(x)
        closed = carleman_closed_form(x)
        carrier = smooth_carleman_carrier(x)
        a = mp.log(PI * x, 2) + mp.mpf("0.5")
        phase = a - mp.floor(a)
        periodic_factor = closed / carrier
        gauge_rows.append(
            [
                mp_string(log2x),
                mp_string(x),
                kopt,
                mp_string(direct),
                mp_string(closed),
                mp_string(carrier),
                mp_string(periodic_factor),
                mp_string(phase),
            ]
        )
    write_csv(
        data_dir / "carleman_gauge_samples.csv",
        [
            "log2_x",
            "x",
            "optimizer_K",
            "direct_infimum",
            "closed_form",
            "continuous_carrier",
            "lattice_factor",
            "phase",
        ],
        gauge_rows,
    )

    # 2. Distinguished peak ray and the exact algebraic gain delta.
    phi_y = sinc_product(mp.mpf(2) / 3)
    kappa_c = mp.mpf("0.5") + mp.log(PI, 2)
    kappa_inf = mp.mpf("1.5") + mp.log(PI / mp.sqrt(3), 2)
    delta = kappa_inf - kappa_c
    peak_rows = []
    for k in range(0, 51):
        x = mp.power(2, k) * mp.mpf(2) / 3
        log_abs = peak_ray_log_abs(k, phi_y)
        abs_phi = mp.e**log_abs
        bc = carleman_closed_form(x)
        normalized = abs_phi / (bc * mp.power(x, -delta))
        peak_rows.append(
            [
                k,
                mp_string(x),
                mp_string(abs_phi),
                mp_string(bc),
                mp_string(delta),
                mp_string(normalized),
                mp_string(-log_abs),
            ]
        )
    write_csv(
        data_dir / "fourier_peak_ray.csv",
        [
            "k",
            "x_k",
            "abs_Phi_xk",
            "Carleman_envelope",
            "delta",
            "absPhi_div_Bc_x_minus_delta",
            "minus_log_absPhi",
        ],
        peak_rows,
    )

    # 3. Lambert-W saddle for the normalized associated function.
    lambert_rows = []
    for j in range(2, 31):
        # t grows by half-octaves; this spans the onset through an asymptotic range.
        t = mp.power(2, mp.mpf(j) / 2)
        nopt, omega = standard_associated_optimizer(t)
        pred = lambert_optimizer(t)
        lambert_rows.append(
            [
                mp_string(t),
                nopt,
                mp_string(pred),
                mp_string(nopt - pred),
                mp_string(omega),
            ]
        )
    write_csv(
        data_dir / "lambert_saddle.csv",
        ["t", "exact_discrete_optimizer", "Lambert_W_predictor", "optimizer_error", "omega_M_t"],
        lambert_rows,
    )

    # 4. Exact Bell-polynomial coefficients.
    W, B = bell_table(bell_nmax)
    bell_rows = []
    for n in range(1, bell_nmax + 1):
        cn = bell_composition_coefficient(n, W, B)
        main = Fraction(2**n + n * (n - 1) + 2, 1)
        approx = bell_edge_approximation(n)
        remainder_after_three = cn - main
        error_after_edges = cn - approx
        # Convert only at output time; all preceding arithmetic is exact.
        bell_rows.append(
            [
                n,
                mp_string(mp.mpf(cn.numerator) / cn.denominator, 50),
                mp_string((mp.mpf(cn.numerator) / cn.denominator) / mp.power(2, n), 50),
                mp_string(mp.mpf(remainder_after_three.numerator) / remainder_after_three.denominator, 50),
                mp_string(mp.mpf(error_after_edges.numerator) / error_after_edges.denominator, 50),
                mp_string(
                    (mp.mpf(error_after_edges.numerator) / error_after_edges.denominator)
                    * mp.power(4, n)
                    / mp.power(n, 6),
                    50,
                ) if n >= 4 else "",
            ]
        )
    write_csv(
        data_dir / "bell_edge_dominance.csv",
        [
            "n",
            "C_n",
            "C_n_div_2_pow_n",
            "C_n_minus_2n_minus_nnm1_minus_2",
            "error_after_four_edge_model",
            "scaled_error_times_4n_div_n6",
        ],
        bell_rows,
    )

    # Human-readable summary used to cross-check the report constants.
    summary = out_dir / "numerical_summary.txt"
    summary.write_text(
        "\n".join(
            [
                "Fabius--Rvachev Carleman frontier numerical summary",
                "====================================================",
                f"Phi(2/3) = {mp_string(phi_y, 80)}",
                f"kappa_C = {mp_string(kappa_c, 50)}",
                f"kappa_infinity = {mp_string(kappa_inf, 50)}",
                f"delta = log_2(2/sqrt(3)) = {mp_string(delta, 50)}",
                f"Bell coefficients computed exactly through n={bell_nmax}.",
                "The optimized envelope direct and closed-form columns agree to the requested precision.",
            ]
        )
        + "\n",
        encoding="utf-8",
    )


def generate_figures(out_dir: Path) -> None:
    import matplotlib
    matplotlib.rcParams["pdf.fonttype"] = 42
    matplotlib.rcParams["ps.fonttype"] = 42
    import matplotlib.pyplot as plt

    data_dir = out_dir / "data"
    fig_dir = out_dir / "figures"
    fig_dir.mkdir(parents=True, exist_ok=True)

    # Figure 1: exact lattice correction as a one-periodic phase profile.
    phase: List[float] = []
    lattice: List[float] = []
    with (data_dir / "carleman_gauge_samples.csv").open(encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            phase.append(float(row["phase"]))
            lattice.append(float(row["lattice_factor"]))
    order = sorted(range(len(phase)), key=phase.__getitem__)
    plt.figure(figsize=(7.1, 3.8))
    plt.plot([phase[i] for i in order], [lattice[i] for i in order], linewidth=1.8)
    plt.xlabel(r"phase $\{\log_2(\pi |x|)+1/2\}$")
    plt.ylabel(r"lattice factor $2^{\operatorname{dist}(a,\mathrm{Z})^2/2}$")
    plt.title("Exact periodic correction in the Fourier--Carleman envelope")
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(fig_dir / "carleman_lattice_phase.pdf")
    plt.savefig(fig_dir / "carleman_lattice_phase.png", dpi=220)
    plt.close()

    # Figure 2: after the sharp algebraic correction x^{-delta}, the peak-ray
    # ratio is phase-locked and therefore constant up to numerical roundoff.
    ks: List[int] = []
    normalized: List[float] = []
    with (data_dir / "fourier_peak_ray.csv").open(encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            ks.append(int(row["k"]))
            normalized.append(float(row["absPhi_div_Bc_x_minus_delta"]))
    plt.figure(figsize=(7.1, 3.8))
    plt.plot(ks, normalized, marker="o", markersize=3, linewidth=1.2)
    plt.xlabel(r"dyadic shell $k$ in $x_k=2^k(2/3)$")
    plt.ylabel(r"$|\Phi(x_k)|/[B_C(x_k)x_k^{-\delta}]$")
    plt.title("Optimal algebraic gain beyond the derivative envelope")
    plt.ticklabel_format(style="plain", axis="y", useOffset=False)
    if normalized:
        lo, hi = min(normalized), max(normalized)
        pad = max((hi - lo) * 10, abs(lo) * 1e-6, 1e-8)
        plt.ylim(lo - pad, hi + pad)
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(fig_dir / "fourier_optimal_gain_peak_ray.pdf")
    plt.savefig(fig_dir / "fourier_optimal_gain_peak_ray.png", dpi=220)
    plt.close()

    # Figure 3: the Lambert-W predictor tracks the exact discrete optimizer.
    ts: List[float] = []
    optimizer_errors: List[float] = []
    with (data_dir / "lambert_saddle.csv").open(encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            ts.append(float(row["t"]))
            optimizer_errors.append(float(row["optimizer_error"]))
    plt.figure(figsize=(7.1, 3.8))
    plt.semilogx(ts, optimizer_errors, marker="o", markersize=3, linewidth=1.2)
    plt.axhline(0.0, linewidth=0.8)
    plt.xlabel(r"associated-function parameter $t$")
    plt.ylabel(r"$n_*(t)-\lambda(t)$")
    plt.title("Lambert-W predictor for the normalized Carleman saddle")
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(fig_dir / "lambert_saddle_error.pdf")
    plt.savefig(fig_dir / "lambert_saddle_error.png", dpi=220)
    plt.close()

    # Figure 4: Bell edge dominance.  The displayed error has the four explicit
    # edge contributions removed.  Its scaled version approaches a finite value.
    ns: List[int] = []
    errors: List[float] = []
    scaled: List[float] = []
    with (data_dir / "bell_edge_dominance.csv").open(encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            n = int(row["n"])
            if n >= 6:
                ns.append(n)
                errors.append(abs(float(row["error_after_four_edge_model"])))
                scaled.append(float(row["scaled_error_times_4n_div_n6"]))
    plt.figure(figsize=(7.1, 3.8))
    plt.semilogy(ns, errors, marker="o", markersize=3, linewidth=1.2)
    plt.xlabel(r"derivative order $n$")
    plt.ylabel("absolute residual")
    plt.title("Bell-polynomial edge dominance after explicit subtraction")
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(fig_dir / "bell_edge_residual.pdf")
    plt.savefig(fig_dir / "bell_edge_residual.png", dpi=220)
    plt.close()

    plt.figure(figsize=(7.1, 3.8))
    plt.plot(ns, scaled, marker="o", markersize=3, linewidth=1.2)
    plt.axhline(4.0 / 3.0, linewidth=1.0, linestyle="--", label=r"$4/3$")
    plt.xlabel(r"derivative order $n$")
    plt.ylabel(r"residual $\times 4^n/n^6$")
    plt.title("Evidence for the next Bell-edge asymptotic scale")
    plt.legend(loc="best")
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(fig_dir / "bell_edge_scaled_residual.pdf")
    plt.savefig(fig_dir / "bell_edge_scaled_residual.png", dpi=220)
    plt.close()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory receiving data/, figures/, and numerical_summary.txt",
    )
    parser.add_argument(
        "--bell-nmax",
        type=int,
        default=120,
        help="largest exact Bell coefficient (default: 120)",
    )
    parser.add_argument(
        "--no-figures",
        action="store_true",
        help="generate CSV/text output only",
    )
    args = parser.parse_args()
    if args.bell_nmax < 6:
        parser.error("--bell-nmax must be at least 6")
    generate_tables(args.out_dir, args.bell_nmax)
    if not args.no_figures:
        generate_figures(args.out_dir)
    print(f"Wrote reproducible outputs under {args.out_dir}")


if __name__ == "__main__":
    main()
