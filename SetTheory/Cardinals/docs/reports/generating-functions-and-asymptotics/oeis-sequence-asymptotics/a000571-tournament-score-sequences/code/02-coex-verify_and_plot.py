#!/usr/bin/env python3
"""Exact combinatorial checks and deterministic floating diagnostics.

Run from any directory, using Python 3 with numpy, scipy, matplotlib, mpmath:
    python code/verify_and_plot.py
The default run checks every Landau score sequence of size at most 10 and
plots the weighted giant-component probability at n=512,2000,8000.

The exact combinatorial assertions use Python integers. The numerical plots
use numpy.longdouble recurrences; they are deterministic diagnostics, not
interval computations and not a substitute for the asymptotic proofs.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
import math
from pathlib import Path
import time

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from scipy.special import expit, lambertw
from scipy.signal import fftconvolve


def totients(n: int) -> list[int]:
    phi = list(range(n + 1))
    if n >= 1:
        phi[1] = 1
    for prime in range(2, n + 1):
        if phi[prime] == prime:
            for k in range(prime, n + 1, prime):
                phi[k] -= phi[k] // prime
    return phi


def integer_counts(nmax: int):
    """Exact N_n, S_n and I_n from the divisor and convolution formulas."""
    phi = totients(nmax)
    numerator = [0] * (nmax + 1)
    for d in range(1, nmax + 1):
        central = math.comb(2 * d, d)
        for n in range(d, nmax + 1, d):
            numerator[n] += (-1 if (n + d) % 2 else 1) * phi[n // d] * central
    aux = [0] * (nmax + 1)
    scores = [1] + [0] * nmax
    strong = [0] * (nmax + 1)
    for n in range(1, nmax + 1):
        assert numerator[n] % (2 * n) == 0
        aux[n] = numerator[n] // (2 * n)
        value = sum(aux[k] * scores[n - k] for k in range(1, n + 1))
        assert value % n == 0
        scores[n] = value // n
        strong[n] = scores[n] - sum(
            strong[k] * scores[n - k] for k in range(1, n)
        )
        assert strong[n] >= 0
    return aux, scores, strong


def exact_checks(nmax: int = 10) -> dict:
    """Independent Landau enumeration checks whole polynomials, not samples."""
    aux, scores, strong = integer_counts(nmax)
    blocks = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    blocks[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            blocks[n][k] = sum(
                strong[j] * blocks[n - j][k - 1] for j in range(1, n + 1)
            )

    # H=[z^n u^k] (1-u I(z))^(-2), using independent polynomial convolution.
    square = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    for n in range(nmax + 1):
        for a in range(n + 1):
            for ka in range(a + 1):
                for kb in range(n - a + 1):
                    square[n][ka + kb] += blocks[a][ka] * blocks[n - a][kb]
    giant_formula = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    for n in range(1, nmax + 1):
        for j in range(n // 2 + 1, n + 1):
            for k in range(1, n + 1):
                giant_formula[n][k] += strong[j] * square[n - j][k - 1]

    rows = []
    candidates_tested = 0
    for n in range(1, nmax + 1):
        observed_blocks = [0] * (nmax + 1)
        observed_giant = [0] * (nmax + 1)
        target = n * (n - 1) // 2
        for score in itertools.combinations_with_replacement(range(n), n):
            candidates_tested += 1
            if sum(score) != target:
                continue
            cumulative = 0
            equalities = []
            valid = True
            for j, value in enumerate(score, 1):
                cumulative += value
                threshold = j * (j - 1) // 2
                if cumulative < threshold:
                    valid = False
                    break
                if cumulative == threshold:
                    equalities.append(j)
            if not valid:
                continue
            k = len(equalities)
            observed_blocks[k] += 1
            sizes = [b - a for a, b in zip([0] + equalities, equalities)]
            if max(sizes) > n / 2:
                observed_giant[k] += 1
        assert sum(observed_blocks) == scores[n], (n, "all scores")
        assert observed_blocks[1] == strong[n], (n, "strong scores")
        assert observed_blocks == blocks[n], (n, "block polynomial")
        assert observed_giant == giant_formula[n], (n, "giant polynomial")
        rows.append({
            "n": n, "N_n": aux[n], "S_n": scores[n], "I_n": strong[n],
            "blocks_polynomial_coefficients": observed_blocks[:n + 1],
            "giant_polynomial_coefficients": observed_giant[:n + 1],
            "giant_count_at_weight_1": sum(observed_giant),
        })
    return {
        "status": "all exact integer assertions passed",
        "n_max": nmax,
        "monotone_candidate_sequences_tested": candidates_tested,
        "assertions": [
            "The divisor numerator is divisible by 2n.",
            "The S_n recurrence numerator is divisible by n.",
            "Landau enumeration agrees with S_n and I_n.",
            "Every coefficient of the component-count polynomial agrees.",
            "Every coefficient of the giant-block polynomial agrees with the marked-block identity.",
        ],
        "rows": rows,
    }


def constants(remainder_cutoff: int = 200) -> dict:
    """Exact remainder numerators and high precision decimal evaluation.

    Explicit tail bounds are mathematical bounds for the omitted series.
    Decimal evaluations of pi/log/exp use mpmath and are not interval bounds.
    """
    mp.mp.dps = 90
    aux, _, _ = integer_counts(remainder_cutoff)
    lam = mp.pi**2 / 12 - mp.log(2)**2
    mu = mp.log(2)
    for n in range(1, remainder_cutoff + 1):
        numerator = 2 * n * aux[n] - math.comb(2 * n, n)
        term = mp.mpf(numerator) / (2 * n**2 * mp.mpf(4)**n)
        lam += term
        mu += n * term
    p = -mp.expm1(-lam)
    mean = mp.exp(-lam) * mu / p
    amplitude = mp.exp(-lam) / (2 * mp.sqrt(mp.pi) * p)
    return {
        "lambda": mp.nstr(lam, 65),
        "mu": mp.nstr(mu, 65),
        "p": mp.nstr(p, 65),
        "critical_weight": mp.nstr(1 / p, 65),
        "mean_m": mp.nstr(mean, 65),
        "tail_amplitude_d": mp.nstr(amplitude, 65),
        "stable_laplace_coefficient_a": mp.nstr(4 * mp.sqrt(mp.pi) * amplitude / 3, 65),
        "remainder_cutoff": remainder_cutoff,
        "lambda_series_tail_bound": mp.nstr(mp.mpf(2)**(-remainder_cutoff - 1), 15),
        "mu_series_tail_bound": mp.nstr((remainder_cutoff + 2) * mp.mpf(2)**(-remainder_cutoff - 1), 15),
        "arithmetic_note": "Series-tail bounds are rigorous; displayed decimal evaluations are non-interval mpmath computations.",
    }


def normalized_counts(nmax: int, const: dict):
    """Scale before recursing, preventing exponential growth and overflow.

    nu_n=N_n/4^n; s_n=S_n/4^n; i_n=I_n/4^n.
    n s_n=sum nu_j s_(n-j).
    n i_n=nu_n-sum_(j<n) nu_j i_(n-j).
    The latter follows by differentiating I=1-exp(-A).
    The first 200 divisor coefficients are formed from exact integers.
    For higher n, the proper-divisor remainder is smaller than 2^(-n-1)
    in A(z/4), and is below long-double accuracy at the chosen cutoff.
    """
    ld = np.longdouble
    cutoff = min(200, nmax)
    aux, exact_scores, exact_strong = integer_counts(cutoff)
    central = np.ones(nmax + 1, dtype=ld)
    for n in range(1, nmax + 1):
        central[n] = central[n - 1] * (1 - ld(1) / (2 * n))
    nu = np.zeros(nmax + 1, dtype=ld)
    index = np.arange(1, nmax + 1, dtype=ld)
    nu[1:] = central[1:] / (2 * index)
    for n in range(1, cutoff + 1):
        nu[n] = ld(str(aux[n])) * np.exp2(ld(-2 * n))
    all_scores = np.zeros(nmax + 1, dtype=ld)
    strong = np.zeros(nmax + 1, dtype=ld)
    all_scores[0] = 1
    for n in range(1, nmax + 1):
        all_scores[n] = np.dot(nu[1:n + 1], all_scores[n - 1::-1]) / n
        strong[n] = (nu[n] - np.dot(nu[1:n], strong[n - 1:0:-1])) / n
    assert np.min(strong) >= 0
    assert strong[2] == 0 if nmax >= 2 else True
    p = ld(const["p"])
    q = strong / p

    score_errors, strong_errors, second_recurrence_errors = [], [], []
    for n in range(1, cutoff + 1):
        scale = np.exp2(ld(-2 * n))
        expected_s = ld(str(exact_scores[n])) * scale
        expected_i = ld(str(exact_strong[n])) * scale
        score_errors.append(abs(all_scores[n] / expected_s - 1))
        if expected_i:
            strong_errors.append(abs(strong[n] / expected_i - 1))
    check_indices = sorted(set(range(1, min(nmax, 30) + 1)) | set(np.linspace(31, nmax, 30).astype(int)))
    for n in check_indices:
        alternative = all_scores[n] - np.dot(strong[1:n], all_scores[n - 1:0:-1])
        if strong[n]:
            second_recurrence_errors.append(abs(alternative / strong[n] - 1))
    diag = {
        "dtype": "numpy.longdouble",
        "mantissa_bits": int(np.finfo(ld).nmant),
        "n_max": nmax,
        "exact_divisor_coefficients_through": cutoff,
        "max_relative_score_error_against_exact_integers": float(max(score_errors)),
        "max_relative_strong_error_against_exact_integers": float(max(strong_errors)),
        "max_relative_difference_from_second_strong_recurrence": float(max(second_recurrence_errors)),
        "q_truncated_total_mass": float(q.sum()),
        "q_truncated_mean": float(np.dot(np.arange(nmax + 1, dtype=ld), q)),
        "predicted_mass_deficit_leading_term": float(2 * ld(const["tail_amplitude_d"]) / (3 * ld(nmax)**ld(1.5))),
        "predicted_mean_deficit_leading_term": float(2 * ld(const["tail_amplitude_d"]) / np.sqrt(ld(nmax))),
        "q_n_times_n_power_5_over_2_divided_by_d_at_n_max": float(q[-1] * ld(nmax)**ld(2.5) / ld(const["tail_amplitude_d"])),
        "warning": "Floating diagnostics, including their differences, are not certified error enclosures.",
    }
    return q, all_scores, strong, diag


def weighted_coefficients(q: np.ndarray, n: int, r: np.longdouble):
    z = np.zeros(n + 1, dtype=np.longdouble)
    z[0] = 1
    for k in range(1, n + 1):
        z[k] = r * np.dot(q[1:k + 1], z[k - 1::-1])
    half = (n - 1) // 2  # complement of a block of size strictly greater than n/2
    squared = np.convolve(z[:half + 1], z[:half + 1])[:half + 1]
    giant = r * np.dot(q[n:n - half - 1:-1], squared)
    return z, giant


def write_csv(path: Path, rows: list[dict]):
    with path.open("w", newline="", encoding="utf8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def coexistence_diagnostics(q: np.ndarray, const: dict, sizes: list[int], offsets: np.ndarray):
    mean = np.longdouble(const["mean_m"])
    amplitude = np.longdouble(const["tail_amplitude_d"])
    rows = []
    for n in sizes:
        t = -2 * lambertw(-0.5 * math.sqrt(float(amplitude / mean)) * n**(-0.25), -1).real
        for offset in offsets:
            tau = np.longdouble(t + offset)
            if tau <= 0:
                continue
            r = 1 / (1 + mean * tau / n)
            z, giant = weighted_coefficients(q, n, r)
            probability = giant / z[n]
            assert 0 <= probability <= 1 + 5e-15
            # Two leading coefficients, retaining the finite-n tau dependence.
            collective = np.exp(-tau) / (r * mean)
            big = r * amplitude * np.longdouble(n)**np.longdouble(-2.5) / (1 - r)**2
            corrected = big / (collective + big)
            rows.append({
                "n": n,
                "offset_s": float(offset),
                "balance_center_t_n": float(t),
                "tau": float(tau),
                "r": float(r),
                "component_weight_u": float(r / np.longdouble(const["p"])),
                "Z_n_floating": float(z[n]),
                "B_n_floating": float(giant),
                "giant_probability_floating": float(probability),
                "logistic_limit": float(expit(offset)),
                "finite_n_two_term_prediction": float(corrected),
                "Z_n_over_two_term_prediction": float(z[n] / (collective + big)),
                "B_n_over_big_jump_prediction": float(giant / big),
                "collective_component_scale_n_over_m": float(n / mean),
                "giant_remainder_scale_n_over_tau": float(n / tau),
                "giant_component_count_scale_n_over_m_tau": float(n / (mean * tau)),
            })
        print(f"Completed deterministic weighted recurrences at n={n}.", flush=True)
    return rows


def plots(rows: list[dict], const: dict, destination: Path):
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 10,
        "axes.spines.top": False, "axes.spines.right": False,
        "savefig.bbox": "tight", "axes.titlesize": 12,
    })
    sizes = sorted(set(row["n"] for row in rows))
    colors = ["#b64b36", "#358571", "#2f5c9c", "#8266a6"]
    fig, ax = plt.subplots(figsize=(7.0, 4.5))
    for color, n in zip(colors, sizes):
        selected = [row for row in rows if row["n"] == n]
        ax.plot([row["offset_s"] for row in selected],
                [row["giant_probability_floating"] for row in selected],
                color=color, lw=2, label=f"Recurrences, n = {n:,}")
    domain = np.linspace(min(row["offset_s"] for row in rows), max(row["offset_s"] for row in rows), 400)
    ax.plot(domain, expit(domain), color="#222222", ls="--", lw=1.7,
            label=r"Limit $e^s/(1+e^s)$")
    selected = [row for row in rows if row["n"] == sizes[-1]]
    ax.plot([row["offset_s"] for row in selected],
            [row["finite_n_two_term_prediction"] for row in selected],
            color="#666666", ls=":", lw=1.6,
            label=f"Two-term prediction, n = {sizes[-1]:,}")
    ax.set(xlabel=r"Offset $s$ from the implicit leading-balance center $t_n$",
           ylabel=r"Probability of a block larger than $n/2$",
           ylim=(0, 1), title="Conditional coexistence: finite-size diagnostics")
    ax.grid(alpha=0.17)
    ax.legend(frameon=False, fontsize=9, loc="upper left")
    fig.tight_layout()
    fig.savefig(destination / "giant_probability.pdf")
    fig.savefig(destination / "giant_probability.png", dpi=190)
    plt.close(fig)


def component_distribution(q: np.ndarray, const: dict, n: int, destination: Path):
    """Numerical joint law of block count and existence of a giant block.

    Powers of rQ are multiplied by FFT; direct positive renewal recurrences
    independently check their aggregate. FFT roundoff is recorded separately.
    """
    ld = np.longdouble
    mean = ld(const["mean_m"])
    amplitude = ld(const["tail_amplitude_d"])
    center = -2 * lambertw(-0.5 * math.sqrt(float(amplitude / mean)) * n**(-0.25), -1).real
    r = 1 / (1 + mean * ld(center) / n)
    z, giant = weighted_coefficients(q, n, r)
    kernel = r * q[:n + 1]
    previous = np.zeros(n + 1, dtype=ld)
    previous[0] = 1
    half = (n - 1) // 2
    total = np.zeros(n + 1, dtype=ld)
    joint_giant = np.zeros(n + 1, dtype=ld)
    clipped_negative_mass = ld(0)
    for k in range(1, n + 1):
        joint_giant[k] = k * r * np.dot(q[n:n - half - 1:-1], previous[:half + 1])
        current = fftconvolve(previous, kernel)[:n + 1]
        current[:k] = 0  # exact minimum possible total size of k blocks
        clipped_negative_mass += -current[current < 0].sum()
        current[current < 0] = 0
        total[k] = current[n]
        previous = current
    total_error = abs(total.sum() / z[n] - 1)
    giant_error = abs(joint_giant.sum() / giant - 1)
    assert total_error < 1e-10
    assert giant_error < 1e-10
    assert np.min(total - joint_giant) > -1e-14 * z[n]
    joint_collective = np.maximum(0, total - joint_giant)
    rows = [{"n": n, "k": k, "offset_s": 0,
             "P_K_floating": float(total[k] / z[n]),
             "P_K_and_giant_floating": float(joint_giant[k] / z[n]),
             "P_K_and_no_giant_floating": float(joint_collective[k] / z[n])}
            for k in range(1, n + 1)]
    x = np.arange(n + 1)
    fig, ax = plt.subplots(figsize=(7.0, 4.3))
    ax.fill_between(x, 0, np.asarray(joint_giant / z[n], dtype=float),
                    color="#2f5c9c", alpha=0.18)
    ax.plot(x, joint_giant / z[n], color="#2f5c9c", lw=1.7,
            label=r"Joint mass: $K_n=k$ and a block $>n/2$")
    ax.fill_between(x, 0, np.asarray(joint_collective / z[n], dtype=float),
                    color="#b64b36", alpha=0.18)
    ax.plot(x, joint_collective / z[n], color="#b64b36", lw=1.7,
            label=r"Joint mass: $K_n=k$ and no block $>n/2$")
    ax.axvline(float(n / mean), color="#888888", ls=":", lw=1.2,
               label=r"Collective scale $n/m$")
    ax.set(xlabel=r"Number of strong blocks $k$", ylabel="Probability mass",
           title=f"Two component-count regimes at n = {n:,}, s = 0",
           xlim=(0, min(n, float(1.35 * n / mean))))
    ax.legend(frameon=False, fontsize=9)
    ax.grid(alpha=0.17)
    fig.tight_layout()
    fig.savefig(destination / "component_count_distribution.pdf")
    fig.savefig(destination / "component_count_distribution.png", dpi=190)
    plt.close(fig)
    diagnostic = {
        "n": n, "offset_s": 0,
        "balance_center_t_n": float(center),
        "relative_total_difference_fft_vs_positive_recurrence": float(total_error),
        "relative_giant_difference_fft_vs_positive_recurrence": float(giant_error),
        "accumulated_negative_fft_roundoff_clipped": float(clipped_negative_mass),
        "giant_probability": float(giant / z[n]),
        "conditional_mean_K_given_giant": float(np.dot(x, joint_giant) / joint_giant.sum()),
        "conditional_mean_K_given_no_giant": float(np.dot(x, joint_collective) / joint_collective.sum()),
        "leading_giant_conditional_mean_prediction": float(2 * n / (mean * center)),
        "leading_collective_component_count_prediction": float(n / mean),
        "warning": "This FFT computation is a non-interval diagnostic; the aggregate checks compare two floating algorithms.",
    }
    return rows, diagnostic


def phase_profiles(destination: Path):
    fig, axes = plt.subplots(1, 2, figsize=(8.8, 3.7))
    x = np.linspace(0, 9, 500)
    axes[0].plot(x, x * np.exp(-x), color="#2f5c9c", lw=2)
    axes[0].set(xlabel=r"$x=\tau_n(n-M_n)/n$", ylabel="Limiting density",
                title=r"Giant phase: $\mathrm{Gamma}(2,1)$ remainder")
    axes[0].fill_between(x, x * np.exp(-x), alpha=0.10, color="#2f5c9c")
    y = np.linspace(0.08, 5, 500)
    frechet = 1.5 * y**(-2.5) * np.exp(-y**(-1.5))
    axes[1].plot(y, frechet, color="#358571", lw=2)
    axes[1].set(xlabel=r"$y=M_n/(2dn/(3m))^{2/3}$", ylabel="Limiting density",
                title="Collective phase: Fréchet maximum")
    axes[1].fill_between(y, frechet, alpha=0.10, color="#358571")
    for ax in axes:
        ax.grid(alpha=0.17)
    fig.suptitle("Asymptotic phase profiles (theoretical densities)", fontsize=12)
    fig.tight_layout()
    fig.savefig(destination / "phase_profiles.pdf")
    fig.savefig(destination / "phase_profiles.png", dpi=190)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact-n", type=int, default=10)
    parser.add_argument("--sizes", type=int, nargs="+", default=[512, 2000, 8000])
    parser.add_argument("--offset-points", type=int, default=33)
    parser.add_argument("--component-n", type=int, default=1000)
    parser.add_argument("--output-root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    start = time.monotonic()
    root = args.output_root
    (root / "data").mkdir(parents=True, exist_ok=True)
    (root / "figures").mkdir(parents=True, exist_ok=True)
    exact = exact_checks(args.exact_n)
    const = constants()
    q, scores, strong, floating = normalized_counts(max(max(args.sizes), args.component_n), const)
    offsets = np.linspace(-4, 4, args.offset_points)
    rows = coexistence_diagnostics(q, const, sorted(args.sizes), offsets)
    write_csv(root / "data" / "coexistence_diagnostics.csv", rows)
    selected_indices = sorted(set([1, 2, 3, 4, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 4000, 8000]) & set(range(1, len(q))))
    qrows = [{"n": n, "q_n_floating": float(q[n]),
              "S_n_over_4_power_n_floating": float(scores[n]),
              "I_n_over_4_power_n_floating": float(strong[n]),
              "q_n_times_n_power_5_over_2_divided_by_d": float(q[n] * np.longdouble(n)**np.longdouble(2.5) / np.longdouble(const["tail_amplitude_d"]))}
             for n in selected_indices]
    write_csv(root / "data" / "normalized_counts.csv", qrows)
    # Use numpy's formatter directly to preserve long-double precision.
    with (root / "data" / "renewal_mass.csv").open("w", encoding="utf8") as handle:
        handle.write("n,q_n_floating\n")
        for n, value in enumerate(q):
            decimal = np.format_float_scientific(value, precision=21, unique=False)
            handle.write(f"{n},{decimal}\n")
    plots(rows, const, root / "figures")
    phase_profiles(root / "figures")
    krows, kdiagnostic = component_distribution(q, const, args.component_n, root / "figures")
    write_csv(root / "data" / "component_count_distribution.csv", krows)
    report = {"exact_checks": exact, "constants": const, "floating_diagnostics": floating,
              "component_distribution_diagnostics": kdiagnostic,
              "selected_coexistence_rows": [row for row in rows if abs(row["offset_s"]) < 1e-12],
              "elapsed_seconds": time.monotonic() - start}
    (root / "data" / "verification_summary.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
