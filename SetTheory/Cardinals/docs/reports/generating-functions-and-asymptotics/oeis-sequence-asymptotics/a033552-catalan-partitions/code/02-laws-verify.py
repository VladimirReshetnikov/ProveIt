#!/usr/bin/env python3
"""Reproduce exact-coefficient diagnostics for Catalan-part partition laws.

Run from any directory:
    python code/verify.py
    python code/verify.py --sizes 100 1000 10000 --no-plots

Required: Python >= 3.10 and mpmath. Optional: matplotlib (figures).
All integer partition counts and moment numerators are exact Python integers.
Saddles, limiting distributions and displayed errors are floating-point
numerical diagnostics, NOT rigorous interval enclosures or asymptotic proofs.
The reported total-variation values use exact coefficients, with floating
summation and an exponentially negligible, non-certified product cutoff.

The distinct Catalan parts start at C_1 = 1.  C_0 must not be added again.
"""

from __future__ import annotations

import argparse
import datetime as dt
import gc
import json
import math
import platform
import sys
import time
from pathlib import Path

import mpmath as mp


OEIS_FIRST_62 = [
    1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 17, 19,
    22, 24, 27, 30, 34, 37, 41, 44, 49, 53, 58, 62, 68, 73,
    80, 85, 92, 98, 106, 113, 121, 128, 137, 145, 155, 163,
    175, 184, 197, 207, 220, 232, 246, 259, 274, 287, 304,
    318, 336, 351, 371, 388, 409, 427, 449, 469,
]
KNOWN_COUNTS = {
    100: 2031,
    1000: 18299196,
    10000: 8125868781802,
    100000: 180507423003606259924,
    1000000: 198409222879647727339514603123,
}
EXPONENTIAL_CUTOFF = 180
PHASE_H_MIN = -28
PHASE_H_MAX = 9


def catalans_through(limit: int) -> list[int]:
    """Distinct C_k <= limit, with k starting at 1."""
    ans = []
    k, c = 1, 1
    while c <= limit:
        ans.append(c)
        c = c * 2 * (2 * k + 1) // (k + 2)
        k += 1
    return ans


def catalans_count(count: int = 200) -> list[int]:
    ans = []
    k, c = 1, 1
    for _ in range(count):
        ans.append(c)
        c = c * 2 * (2 * k + 1) // (k + 2)
        k += 1
    return ans


def coefficients(limit: int, parts: list[int]) -> list[int]:
    p = [1] + [0] * limit
    for c in parts:
        if c > limit:
            break
        for s in range(c, limit + 1):
            p[s] += p[s - c]
    return p


def exact_dp(n: int, cutoffs: list[int]) -> dict:
    """Counts and raw N moments; prefix snapshots also give J and NJ.

    Ascending updates add either no new part or one further copy of c:
      p[s] += p[s-c]
      a[s] += a[s-c] + p[s-c]
      b[s] += b[s-c] + 2*a[s-c] + p[s-c].
    Here a and b sum N and N^2 over the respective partition set.
    """
    parts = catalans_through(n)
    p, a, b = [1] + [0] * n, [0] * (n + 1), [0] * (n + 1)
    at_n = [(0, 0, 0)]
    prefixes = {}
    if 0 in cutoffs:
        prefixes[0] = p.copy()
    for k, c in enumerate(parts, 1):
        for s in range(c, n + 1):
            old_p, old_a = p[s - c], a[s - c]
            p[s] += old_p
            a[s] += old_a + old_p
            b[s] += b[s - c] + 2 * old_a + old_p
        at_n.append((p[n], a[n], b[n]))
        if k in cutoffs:
            prefixes[k] = p.copy()
    total_j = total_j2 = total_nj = 0
    for k in range(1, len(at_n)):
        delta_p = at_n[k][0] - at_n[k - 1][0]
        delta_a = at_n[k][1] - at_n[k - 1][1]
        total_j += k * delta_p
        total_j2 += k * k * delta_p
        total_nj += k * delta_a
    ans = {
        "parts": parts,
        "p": p[n],
        "sum_N": a[n],
        "sum_N2": b[n],
        "sum_J": total_j,
        "sum_J2": total_j2,
        "sum_NJ": total_nj,
        "prefix_at_n": at_n,
        "prefix_arrays": prefixes,
    }
    del p, a, b
    return ans


def enumerate_small(n: int, parts: list[int]) -> list[tuple[int, int]]:
    """Independent exhaustive multiplicity enumeration: output (N,J)."""
    out = []

    def rec(k: int, remainder: int, number: int, largest: int) -> None:
        if k < 0:
            if remainder == 0:
                out.append((number, largest))
            return
        c = parts[k]
        for copies in range(remainder // c + 1):
            rec(k - 1, remainder - copies * c, number + copies,
                max(largest, k + 1) if copies else largest)

    rec(len(parts) - 1, n, 0, 0)
    return out


def finite_crosschecks(all_parts: list[int]) -> dict:
    terms = coefficients(300, catalans_through(300))
    assert terms[:62] == OEIS_FIRST_62
    # Independent logarithmic-derivative recurrence n*p(n)=sum b(j)*p(n-j).
    divisor_weights = [0] * 301
    for c in catalans_through(300):
        for s in range(c, 301, c):
            divisor_weights[s] += c
    recurrence = [1]
    for n in range(1, 301):
        value = sum(divisor_weights[j] * recurrence[n - j]
                    for j in range(1, n + 1))
        assert value % n == 0
        recurrence.append(value // n)
    assert recurrence == terms
    # Exhaustive enumeration checks genuinely different code for all moments.
    for n in range(1, 41):
        obj = exact_dp(n, [])
        states = enumerate_small(n, catalans_through(n))
        observed = (len(states), sum(x for x, _ in states),
                    sum(x * x for x, _ in states),
                    sum(j for _, j in states), sum(j * j for _, j in states),
                    sum(x * j for x, j in states))
        computed = tuple(obj[key] for key in
                         ["p", "sum_N", "sum_N2", "sum_J", "sum_J2", "sum_NJ"])
        assert computed == observed, (n, computed, observed)
    # Full tail-vector enumeration verifies the TV reduction independently.
    # At n=100 the different tail vectors can have the same mass (5*14=14*5).
    n, cutoff = 100, 2
    parts = catalans_through(n)
    vector_counts: dict[tuple[int, ...], int] = {}

    def vector_rec(k: int, remainder: int, multiplicities: list[int]) -> None:
        if k == len(parts):
            if remainder == 0:
                key = tuple(multiplicities[cutoff:])
                vector_counts[key] = vector_counts.get(key, 0) + 1
            return
        for copies in range(remainder // parts[k] + 1):
            vector_rec(k + 1, remainder - copies * parts[k], multiplicities + [copies])

    vector_rec(0, n, [])
    t = mp.mpf("0.08")
    direct_log_f = geometric_sums(t, all_parts, cutoff)["log_product"]
    p_sum = sum(vector_counts.values())
    q_values, differences = [], []
    for vector, count in vector_counts.items():
        mass = sum(copies * c for copies, c in zip(vector, parts[cutoff:]))
        q = float(mp.exp(-t * mass - direct_log_f))
        q_values.append(q)
        differences.append(abs(count / p_sum - q))
    direct_tv = (math.fsum(differences) + 1 - math.fsum(q_values)) / 2
    collapsed_tv = tv_from_coefficients(n, cutoff, t, p_sum,
                                        coefficients(n, parts[:cutoff]), all_parts)["tv"]
    assert abs(direct_tv - collapsed_tv) < 2e-14
    return {
        "oeis_first_terms_matched": 62,
        "log_derivative_recurrence_through_n": 300,
        "exhaustive_enumeration_all_moments_through_n": 40,
        "tail_vector_TV_enumeration_n": n,
        "tail_vector_TV_enumeration_K": cutoff,
        "tail_vector_TV_parameter_t": str(t),
        "tail_vector_TV_direct": direct_tv,
        "tail_vector_TV_mass_collapsed": collapsed_tv,
        "terms_0_through_61": terms[:62],
        "source": "https://oeis.org/A033552",
        "source_inspected_utc_date": "2026-10-05",
    }


def r_of_x(x: mp.mpf) -> mp.mpf:
    return (x * mp.log(4) - mp.log(mp.pi) / 2
            + mp.loggamma(x + mp.mpf("0.5")) - mp.loggamma(x + 2))


def geometric_sums(t: mp.mpf, all_parts: list[int], start: int = 0) -> dict:
    energy = number = log_product = variance_energy = mp.mpf(0)
    used = 0
    for c in all_parts[start:]:
        u = t * c
        if u > EXPONENTIAL_CUTOFF:
            break
        q = mp.exp(-u)
        denominator = -mp.expm1(-u)
        mean = q / denominator
        energy += c * mean
        number += mean
        log_product -= mp.log(denominator)
        variance_energy += u * u * q / (denominator * denominator)
        used += 1
    return {"energy": energy, "number": number, "log_product": log_product,
            "scaled_energy_variance": variance_energy, "factors_used": used}


def saddle(n: int, all_parts: list[int]) -> tuple[mp.mpf, mp.mpf]:
    lo, hi = mp.mpf(0), mp.mpf(1)
    while geometric_sums(hi, all_parts)["energy"] > n:
        hi *= 2
    for _ in range(mp.mp.dps * 4 + 40):
        mid = (lo + hi) / 2
        if geometric_sums(mid, all_parts)["energy"] > n:
            lo = mid
        else:
            hi = mid
    t = (lo + hi) / 2
    target = -mp.log(t)
    lo = mp.mpf(1)
    hi = max(mp.mpf(4), target / mp.log(4) + 10)
    for _ in range(mp.mp.dps * 4 + 40):
        mid = (lo + hi) / 2
        if r_of_x(mid) < target:
            lo = mid
        else:
            hi = mid
    return t, (lo + hi) / 2


def edge_functions(theta: mp.mpf) -> dict:
    """G_h and coefficient D_h in G_h + D_h/m, plus phase moments."""
    cdfs = {}
    corrections = {}
    g, a, v, ell = mp.mpf(1), mp.mpf(0), mp.mpf(0), mp.mpf(0)
    # Starting beyond hmax is numerically indistinguishable at working dps;
    # these finite tail cutoffs are explicitly not interval enclosures.
    for h in range(PHASE_H_MAX, PHASE_H_MIN - 2, -1):
        j = h + 1
        u = mp.power(4, j - theta)
        if u <= EXPONENTIAL_CUTOFF:
            q = mp.exp(-u)
            den = -mp.expm1(-u)
            g *= den
            a += u * q / den
            v += u * u * q / (den * den)
            ell += (j - theta) * u * q / den
        cdfs[h] = g
        corrections[h] = g * (-a + (v - a * a) / 2 - mp.mpf("1.5") * ell)
    mean = second = mean_d = second_d = gamma = mp.mpf(0)
    # The truncated-energy covariance has the convergent limit sum_h G_h*A_h.
    # The full two-sided energy does not itself define an L2 random variable.
    for h in range(PHASE_H_MIN, PHASE_H_MAX + 1):
        probability = cdfs[h] - cdfs[h - 1]
        delta_probability = corrections[h] - corrections[h - 1]
        mean += h * probability
        second += h * h * probability
        mean_d += h * delta_probability
        second_d += h * h * delta_probability
        # Reconstruct A_h from the defining absolutely convergent sum.
        ah = mp.mpf(0)
        for j in range(h + 1, PHASE_H_MAX + 2):
            u = mp.power(4, j - theta)
            if u > EXPONENTIAL_CUTOFF:
                break
            ah += u / mp.expm1(u)
        gamma += cdfs[h] * ah
    return {
        "cdf": cdfs, "correction": corrections, "mean": mean,
        "variance": second - mean * mean,
        "mean_correction": mean_d,
        "variance_correction": second_d - 2 * mean * mean_d,
        "gamma": gamma,
        "retained_probability": cdfs[PHASE_H_MAX] - cdfs[PHASE_H_MIN - 1],
    }


def gaussian_tv(a: float) -> float:
    if a <= 0:
        return 1.0
    if a >= 1:
        return 0.0
    ratio = -math.log(a) / (1 - a)
    # 2(Phi(sqrt(ratio)) - Phi(sqrt(a*ratio))) == erf difference.
    return (math.erf(math.sqrt(ratio / 2))
            - math.erf(math.sqrt(a * ratio / 2)))


def tv_from_coefficients(n: int, k: int, t: mp.mpf, pn: int,
                         prefix: list[int], all_parts: list[int]) -> dict:
    """L1 distance after reducing configurations to their total tail mass.

    Conditional and Boltzmann probabilities have a likelihood ratio depending
    only on s=tail energy; consequently this scalar sum is exactly the same
    TV distance as that of the full tail vector, before numerical rounding.
    """
    tail = coefficients(n, all_parts[k:])
    log_f = float(geometric_sums(t, all_parts, k)["log_product"])
    t_float = float(t)
    absolute_differences, qs, ps = [], [], []
    for s, bs in enumerate(tail):
        if bs == 0:
            continue
        conditional = (bs * prefix[n - s]) / pn
        boltzmann = bs * math.exp(-t_float * s - log_f)
        ps.append(conditional)
        qs.append(boltzmann)
        absolute_differences.append(abs(conditional - boltzmann))
    mass_p, mass_q = math.fsum(ps), math.fsum(qs)
    assert abs(mass_p - 1) < 3e-14, (n, k, mass_p)
    assert mass_q <= 1 + 3e-14, (n, k, mass_q)
    distance = (math.fsum(absolute_differences) + (1 - mass_q)) / 2
    return {"K": k, "tv": distance, "conditional_mass": mass_p,
            "boltzmann_mass_at_most_n": mass_q,
            "unconditioned_tail_probability_above_n": 1 - mass_q,
            "nonzero_tail_coefficients_at_most_n": len(qs)}


def dec(x: mp.mpf, digits: int = 28) -> str:
    return mp.nstr(x, digits)


def one_size(n: int, all_parts: list[int], s_limit: mp.mpf,
             v_limit: mp.mpf) -> dict:
    began = time.perf_counter()
    t, m = saddle(n, all_parts)
    M = int(mp.floor(m))
    theta = m - M
    # Rounding uses floor(x+1/2), avoiding Python's ties-to-even convention.
    cutoffs = sorted(set(max(1, min(M - 1, int(f * M + 0.5)))
                         for f in (0.25, 0.5, 0.75)))
    obj = exact_dp(n, cutoffs)
    if n in KNOWN_COUNTS:
        assert obj["p"] == KNOWN_COUNTS[n]
    pn = obj["p"]
    mean_n = mp.mpf(obj["sum_N"]) / pn
    var_n = mp.mpf(obj["sum_N2"]) / pn - mean_n * mean_n
    mean_j = mp.mpf(obj["sum_J"]) / pn
    var_j = mp.mpf(obj["sum_J2"]) / pn - mean_j * mean_j
    cov_nj = mp.mpf(obj["sum_NJ"]) / pn - mean_n * mean_j
    phase = edge_functions(theta)
    edge_rows = []
    max_error_0 = max_error_1 = mp.mpf(0)
    for h in range(PHASE_H_MIN, PHASE_H_MAX + 1):
        index = M + h
        if index < 1:
            actual = mp.mpf(0)
        elif index >= len(obj["prefix_at_n"]):
            actual = mp.mpf(1)
        else:
            actual = mp.mpf(obj["prefix_at_n"][index][0]) / pn
        leading = phase["cdf"][h]
        improved = leading + phase["correction"][h] / m
        error_0, error_1 = leading - actual, improved - actual
        max_error_0 = max(max_error_0, abs(error_0))
        max_error_1 = max(max_error_1, abs(error_1))
        if -3 <= h <= 3:
            edge_rows.append({"h": h, "exact_coefficient_cdf": dec(actual),
                              "leading_cdf": dec(leading),
                              "first_corrected_cdf": dec(improved),
                              "leading_signed_error": dec(error_0),
                              "corrected_signed_error": dec(error_1)})
    answer = {
        "n": n, "t": dec(t), "m": dec(m), "M": M, "theta": dec(theta),
        "nt": dec(n * t),
        "exact_integer_numerators": {key: str(obj[key]) for key in
                                     ["p", "sum_N", "sum_N2", "sum_J",
                                      "sum_J2", "sum_NJ"]},
        "t_mean_N": dec(t * mean_n),
        "t_mean_N_minus_limit": dec(t * mean_n - s_limit),
        "t2_variance_N": dec(t * t * var_n),
        "variance_limit": dec(v_limit),
        "mean_J_minus_m": dec(mean_j - m),
        "phase_mean_minus_theta": dec(phase["mean"] - theta),
        "first_corrected_mean_J_minus_m": dec(
            phase["mean"] - theta + phase["mean_correction"] / m),
        "variance_J": dec(var_j),
        "phase_variance": dec(phase["variance"]),
        "first_corrected_variance_J": dec(
            phase["variance"] + phase["variance_correction"] / m),
        "cov_tN_J": dec(t * cov_nj),
        "edge_cdf_max_absolute_error_leading": dec(max_error_0),
        "edge_cdf_max_absolute_error_first_correction": dec(max_error_1),
        "m2_times_edge_cdf_max_error_corrected": dec(m * m * max_error_1),
        "edge_cdf_selected_rows": edge_rows,
        "total_variation": [],
        "exploratory_unproved_refinements": {
            "status": "Exploratory coefficients only; the accompanying article does not claim these refined theorems.",
            "m2_times_mean_error": dec(m * m * (t * mean_n - s_limit)),
            "variance_first_heuristic": dec(v_limit - (v_limit + s_limit ** 2) / m),
            "m_times_variance_error": dec(m * (t * t * var_n - v_limit)),
            "m_times_cov_tN_J": dec(m * t * cov_nj),
            "mixed_covariance_candidate_at_phase": dec(-s_limit * phase["gamma"]),
        },
    }
    for k in cutoffs:
        tv = tv_from_coefficients(n, k, t, pn, obj["prefix_arrays"][k], all_parts)
        tv["a_K_over_M"] = k / M
        tv["a_K_over_m"] = float(k / m)
        tv["limit_at_K_over_M"] = gaussian_tv(k / M)
        tv["limit_at_K_over_m"] = gaussian_tv(float(k / m))
        tv["signed_error_using_K_over_M"] = tv["tv"] - tv["limit_at_K_over_M"]
        answer["total_variation"].append(tv)
    del obj
    gc.collect()
    answer["runtime_seconds"] = time.perf_counter() - began
    return answer


def latex_number(x: str | float, digits: int = 3) -> str:
    value = float(x)
    if value == 0:
        return "$0$"
    if abs(value) >= 0.001:
        return f"${value:.{digits}f}$"
    mantissa, exponent = f"{value:.{digits}e}".split("e")
    return rf"${mantissa}\times10^{{{int(exponent)}}}$"


def save_tables(data_dir: Path, rows: list[dict]) -> None:
    lines = [r"% Generated by code/verify.py. Exact coefficients, numerical saddles.",
             r"\begin{tabular}{rrrrr}", r"\toprule",
             r"$n$ & $m$ & $t\mathbb E N$ & $t^2\operatorname{Var}N$ & "
             r"$\operatorname{Cov}(tN,J)$\\",
             r"\midrule"]
    for row in rows:
        lines.append(" & ".join([f"${row['n']:,}$", f"${float(row['m']):.4f}$",
                                  *[f"${float(row[key]):.6f}$" for key in
                                    ["t_mean_N", "t2_variance_N", "cov_tN_J"]]]) + r"\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (data_dir / "moments_table.tex").write_text("\n".join(lines) + "\n")

    lines = [r"% Maximum errors over the integer thresholds retained in verification.",
             r"\begin{tabular}{rrrrr}", r"\toprule",
             r"$n$ & $\theta$ & Leading error & "
             r"Corrected error & $m^2$ scaled\\",
             r"\midrule"]
    for row in rows:
        lines.append(" & ".join([f"${row['n']:,}$", f"${float(row['theta']):.4f}$",
                                  latex_number(row["edge_cdf_max_absolute_error_leading"], 6),
                                  latex_number(row["edge_cdf_max_absolute_error_first_correction"], 6),
                                  latex_number(row["m2_times_edge_cdf_max_error_corrected"])])
                     + r"\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (data_dir / "edge_errors_table.tex").write_text("\n".join(lines) + "\n")

    lines = [r"% TV is evaluated from exact coefficients, with floating summation.",
             r"\begin{tabular}{rrrrr}",
             r"\toprule", r"$n$ & $K$ & $a=K/M$ & coefficient TV & $d(a)$\\",
             r"\midrule"]
    for row in rows:
        for tv in row["total_variation"]:
            lines.append(" & ".join([f"${row['n']:,}$", f"${tv['K']}$",
                                      f"${tv['a_K_over_M']:.4f}$",
                                      f"${tv['tv']:.6f}$",
                                      f"${tv['limit_at_K_over_M']:.6f}$"]) + r"\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (data_dir / "tv_table.tex").write_text("\n".join(lines) + "\n")


def make_figures(output_dir: Path, rows: list[dict]) -> dict:
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        return {"created": False, "reason": "matplotlib not installed"}
    fig_dir = output_dir / "figures"
    fig_dir.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({"font.family": "DejaVu Serif", "font.size": 10,
                         "axes.labelsize": 10, "axes.titlesize": 11,
                         "pdf.fonttype": 42, "ps.fonttype": 42,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "figure.dpi": 160, "savefig.dpi": 220})
    xs = [i / 500 for i in range(501)]
    fig, ax = plt.subplots(figsize=(6.6, 3.8), layout="constrained")
    ax.plot(xs, [gaussian_tv(a) for a in xs], color="#173d70", lw=2,
            label=r"Gaussian limit $d(a)$")
    colors = ["#ae6c22", "#6a4c93", "#258070"]
    selected = [rows[0], rows[len(rows) // 2], rows[-1]]
    for color, row in zip(colors, selected):
        ax.scatter([v["a_K_over_M"] for v in row["total_variation"]],
                   [v["tv"] for v in row["total_variation"]],
                   color=color, s=35, zorder=3, label=rf"Exact coefficients, $n={row['n']:,}$")
    ax.set(xlim=(0, 1), ylim=(0, 1.02), xlabel=r"Retained lower fraction $a=K/M$",
           ylabel="Total-variation distance",
           title="Conditioning remains visible for a macroscopic upper block")
    ax.grid(alpha=0.18)
    ax.legend(frameon=False, fontsize=8, loc="upper right")
    for ext in ["pdf", "png"]:
        fig.savefig(fig_dir / f"tv_universality.{ext}")
    plt.close(fig)

    phase_rows = []
    for i in range(201):
        theta = mp.mpf(i) / 200
        obj = edge_functions(theta)
        phase_rows.append({"theta": float(theta),
                           "mean_minus_theta": float(obj["mean"] - theta),
                           "variance": float(obj["variance"]),
                           "gamma": float(obj["gamma"])})
    fig, axes = plt.subplots(2, 1, figsize=(6.6, 4.5), sharex=True,
                             layout="constrained")
    x = [r["theta"] for r in phase_rows]
    axes[0].plot(x, [r["mean_minus_theta"] for r in phase_rows], color="#173d70", lw=2)
    axes[1].plot(x, [r["variance"] for r in phase_rows], color="#258070", lw=2)
    axes[0].set(ylabel=r"$\mathbb{E}H_\theta-\theta$",
                title="Periodic corrections to the largest Catalan index")
    axes[1].set(xlabel=r"Phase $\theta$", ylabel=r"$\mathrm{Var}(H_\theta)$", xlim=(0, 1))
    for ax in axes:
        ax.grid(alpha=0.18)
        ax.ticklabel_format(axis="y", style="plain", useOffset=False)
    for ext in ["pdf", "png"]:
        fig.savefig(fig_dir / f"phase_functions.{ext}")
    plt.close(fig)
    (output_dir / "data" / "phase_functions.json").write_text(
        json.dumps(phase_rows, indent=2) + "\n")
    return {"created": True, "matplotlib_version": matplotlib.__version__,
            "phase_mean_min": min(r["mean_minus_theta"] for r in phase_rows),
            "phase_mean_max": max(r["mean_minus_theta"] for r in phase_rows),
            "phase_variance_min": min(r["variance"] for r in phase_rows),
            "phase_variance_max": max(r["variance"] for r in phase_rows)}


def main() -> None:
    global EXPONENTIAL_CUTOFF
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", nargs="+", type=int,
                        default=[100, 1000, 10000, 100000, 1000000])
    parser.add_argument("--dps", type=int, default=60)
    parser.add_argument("--no-plots", action="store_true")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    if min(args.sizes) < 20:
        parser.error("Use sizes at least 20 for the saddle/phase diagnostics.")
    mp.mp.dps = args.dps
    EXPONENTIAL_CUTOFF = max(180, math.ceil((args.dps + 15) * math.log(10)))
    started = time.perf_counter()
    data_dir = args.output / "data"
    data_dir.mkdir(parents=True, exist_ok=True)
    all_parts = catalans_count(max(200, 2 * args.dps))
    s = 1 + 4 * mp.pi / (9 * mp.sqrt(3))
    reciprocal_sum = mp.fsum(mp.mpf(1) / c for c in all_parts)
    assert abs(s - reciprocal_sum) < mp.mpf(10) ** (-(args.dps - 5))
    v = mp.fsum(mp.mpf(1) / (c * c) for c in all_parts)
    verification = finite_crosschecks(all_parts)
    print("Exact small-n enumeration, recurrence, and 62 OEIS terms: PASS", flush=True)
    rows = []
    for n in sorted(set(args.sizes)):
        row = one_size(n, all_parts, s, v)
        rows.append(row)
        print(f"n={n:,}; m={float(row['m']):.6f}; "
              f"E(tN)={float(row['t_mean_N']):.9f}; "
              f"edge max error {float(row['edge_cdf_max_absolute_error_leading']):.3g} -> "
              f"{float(row['edge_cdf_max_absolute_error_first_correction']):.3g}; "
              f"{row['runtime_seconds']:.2f}s", flush=True)
    save_tables(data_dir, rows)
    figures = {"created": False, "reason": "--no-plots"}
    if not args.no_plots:
        figures = make_figures(args.output, rows)
    output = {
        "description": "Exact integer coefficient and moment calculations with numerical asymptotic diagnostics",
        "certification": "No interval certificates; numerical agreement does not prove asymptotic theorems.",
        "python": sys.version,
        "platform": platform.platform(),
        "mpmath_version": mp.__version__,
        "decimal_precision": args.dps,
        "exponential_product_cutoff": EXPONENTIAL_CUTOFF,
        "phase_threshold_range": [PHASE_H_MIN, PHASE_H_MAX],
        "utc_run_time": dt.datetime.now(dt.timezone.utc).isoformat(),
        "s_limit": dec(s, 50), "variance_limit": dec(v, 50),
        "crosschecks": verification, "sizes": rows, "figures": figures,
        "total_runtime_seconds": time.perf_counter() - started,
    }
    (data_dir / "verification.json").write_text(json.dumps(output, indent=2) + "\n")
    print(f"Wrote data and tables; total runtime {output['total_runtime_seconds']:.2f}s", flush=True)


if __name__ == "__main__":
    main()
