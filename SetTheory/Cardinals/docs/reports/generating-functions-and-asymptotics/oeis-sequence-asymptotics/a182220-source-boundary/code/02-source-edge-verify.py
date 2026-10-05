#!/usr/bin/env python3
"""Reproduce the finite checks and numerical figures for the EAD article.

Run from any working directory:
    python code/verify.py

Exact part: Python integer arithmetic; two independent counting recurrences;
and direct generation of full sets as nested frozensets through size seven.
Numerical part: mpmath, with 100 decimal working digits by default. Exact
finite-defect coefficients are used in the finite block-profile tests. Radial
tests evaluate finitely many blocks and finitely many terms of the late blocks,
with explicit analytic bounds for those omitted tails. Floating-point rounding
is NOT enclosed by interval arithmetic, so the numerical tables are not formal
certificates and do not establish the infinite theorems.

No source files or source-program fixtures are imported. The source-deletion
recurrence and marked-source sieve are independently implemented below.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import platform
import sys
import time
from collections import Counter
from pathlib import Path

import mpmath as mp


def binom(n: int, k: int) -> int:
    return math.comb(n, k) if 0 <= k <= n else 0


def dyadic_index(n: int) -> int:
    """ceil(log_2(n)), computed without floating point, for n >= 1."""
    return (n - 1).bit_length()


def total_counts(max_n: int) -> list[int]:
    u = [1]
    for n in range(1, max_n + 1):
        u.append(sum(
            (-1) ** (t - 1) * binom(2 ** (n - t) - (n - t), t) * u[n - t]
            for t in range(1, n + 1)
        ))
    return u


def source_sieve(n: int, k: int, u: list[int]) -> int:
    return sum(
        (-1) ** (t - k) * binom(t, k)
        * u[n - t] * binom(2 ** (n - t) - (n - t), t)
        for t in range(k, n + 1)
    )


def source_deletion_triangle(max_n: int) -> tuple[list[list[int]], int]:
    """Build from source deletion, without using the total-count recurrence."""
    triangle = [[1], [0, 1]]
    divisibility_checks = 0
    for n in range(2, max_n + 1):
        previous = triangle[n - 1]
        row = [0] * (n + 1)
        for s in range(1, n + 1):
            numerator = (2 ** (n - s) - (n - 1)) * previous[s - 1]
            numerator += sum(
                binom(s + j, j + 1) * 2 ** (n - 1 - s - j) * previous[s + j]
                for j in range(n - s)
            )
            assert numerator % s == 0, (n, s, numerator)
            divisibility_checks += 1
            row[s] = numerator // s
        triangle.append(row)
    return triangle, divisibility_checks


def boundary_count(n: int, d: int, u: list[int]) -> int:
    q = dyadic_index(n)
    m = q + d
    k = n - m
    if k < 1:
        return 0
    return sum(
        (-1) ** h * binom(k + h, h) * u[m - h]
        * binom(2 ** (m - h) - (m - h), k + h)
        for h in range(d + 1)
    )


def full_set_counts(max_n: int) -> list[dict]:
    """Generate full sets by adjoining subsets, without any graph recurrence.

    A full (transitive) finite set F can be extended by F union {S}, where
    S is any subset of F that is not already an element of F. Conversely,
    deleting a membership-maximal element of a nonempty full set reverses
    such a step. Nested frozensets represent the actual hereditarily finite
    sets; deduplication is literal equality, with no graph-isomorphism oracle.
    """
    layer = {frozenset()}
    records = [{"n": 0, "full_sets": 1, "source_row": [1]}]
    for n in range(1, max_n + 1):
        following = set()
        attempted_extensions = 0
        for full_set in layer:
            elements = tuple(full_set)
            for mask in range(1 << len(elements)):
                subset = frozenset(elements[i] for i in range(len(elements))
                                   if mask & (1 << i))
                if subset not in full_set:
                    attempted_extensions += 1
                    following.add(full_set | {subset})
        layer = following
        by_sources = Counter()
        for full_set in layer:
            members_of_members = set()
            for element in full_set:
                members_of_members.update(element)
            assert members_of_members <= full_set
            by_sources[len(full_set - members_of_members)] += 1
        records.append({
            "n": n,
            "full_sets": len(layer),
            "attempted_extensions": attempted_extensions,
            "source_row": [by_sources[k] for k in range(n + 1)],
        })
    return records


def write_csv(path: Path, fieldnames: list[str], rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def decimal(value, digits: int = 45) -> str:
    return mp.nstr(value, digits, strip_zeros=False)


def parameters(d: int):
    a = 2 ** (d + 1)
    radius = mp.mpf(a - 1) ** (a - 1) / mp.mpf(a) ** a
    rho = (mp.mpf(a - 1) / a) ** a
    return a, radius, rho


def exact_block_coefficients(q: int, d: int, u: list[int]) -> tuple[int, list[int]]:
    """Exact b_n along a complete block, using integer adjacent-term ratios."""
    size = 2 ** (q - 1)
    m = q + d
    k0 = size + 1 - m
    if k0 < 1:
        values = [boundary_count(n, d, u) for n in range(size + 1, 2 * size + 1)]
        return 0, values
    universes = [2 ** (m - h) - (m - h) for h in range(d + 1)]
    summands = [binom(k0 + h, h) * u[m - h] * binom(universes[h], k0 + h)
                for h in range(d + 1)]
    leading_first = summands[0]
    coefficients = []
    for j in range(size):
        k = k0 + j
        coefficients.append(sum((-1) ** h * summands[h] for h in range(d + 1)))
        assert coefficients[-1] >= 0
        if j + 1 < size:
            for h in range(d + 1):
                numerator = summands[h] * (universes[h] - k - h)
                assert numerator % (k + 1) == 0
                summands[h] = numerator // (k + 1)
    return leading_first, coefficients


def roots_of_unity() -> list[tuple[str, int, int, mp.mpc]]:
    # The rational angle records let late dyadic-block phases be computed
    # by an exact modular exponent, without powering an approximate root.
    return [
        ("1", 0, 1, mp.mpc(1)),
        ("-1", 1, 2, mp.mpc(-1)),
        ("i", 1, 4, mp.mpc(0, 1)),
        ("-i", 3, 4, mp.mpc(0, -1)),
        ("exp(i*pi/4)", 1, 8, mp.exp(mp.j * mp.pi / 4)),
    ]


def evaluate_polynomial(coefficients, argument):
    value = mp.mpc(0) if isinstance(argument, mp.mpc) else mp.mpf(0)
    for coefficient in reversed(coefficients):
        value = value * argument + coefficient
    return value


def finite_profile_tests(q_min: int, q_max: int, u: list[int], data: Path):
    rows, endpoint_rows, summary_rows = [], [], []
    cache = {}
    roots = roots_of_unity()
    for d in range(4):
        a, radius, rho = parameters(d)
        for q in range(q_min, q_max + 1):
            size = 2 ** (q - 1)
            m = q + d
            leading_first, exact = exact_block_coefficients(q, d, u)
            assert leading_first > 0
            # Check the adjacent-term implementation against direct binomial
            # evaluation at the beginning, middle, and end of every block.
            for j in sorted({0, 1, size // 2, size - 1}):
                assert exact[j] == boundary_count(size + 1 + j, d, u)
            r_power = mp.mpf(1)
            normalized = []
            for coefficient in exact:
                normalized.append(mp.mpf(coefficient) / leading_first * r_power)
                r_power *= radius
            cache[d, q] = (leading_first, exact, normalized)
            coefficient_l1 = mp.fsum(abs(coefficient - rho ** j)
                                    for j, coefficient in enumerate(normalized))
            coefficient_l1 += rho ** size / (1 - rho)
            sampled_errors = []
            for name, _, _, root in roots:
                observed = evaluate_polynomial(normalized, root)
                limit = 1 / (1 - rho * root)
                error = abs(observed - limit)
                sampled_errors.append(error)
                rows.append({
                    "d": d, "q": q, "N": size, "m": m, "w": name,
                    "P_real": decimal(observed.real), "P_imag": decimal(observed.imag),
                    "limit_real": decimal(limit.real), "limit_imag": decimal(limit.imag),
                    "absolute_error": decimal(error),
                })
            c = mp.mpf(leading_first) * radius ** (size + 1)
            asymptotic = (mp.mpf(u[m]) * rho * mp.mpf(a) ** (-m)
                          * mp.sqrt(mp.mpf(a) / (2 * mp.pi * (a - 1) * size)))
            endpoint_rows.append({
                "d": d, "q": q, "N": size, "m": m,
                "c_q": decimal(c), "asymptotic_c_q": decimal(asymptotic),
                "ratio_to_asymptotic": decimal(c / asymptotic),
                "relative_error": decimal(abs(c / asymptotic - 1)),
            })
            summary_rows.append({
                "d": d, "q": q, "N": size, "m": m,
                "max_sampled_error": decimal(max(sampled_errors)),
                "coefficient_l1_upper_bound": decimal(coefficient_l1),
                "l1_bound_times_N_over_m": decimal(coefficient_l1 * size / m),
                "relative_endpoint_covering_deficit": decimal(
                    mp.mpf(leading_first - exact[0]) / leading_first),
            })
    write_csv(data / "profiles.csv", list(rows[0]), rows)
    write_csv(data / "profile_summary.csv", list(summary_rows[0]), summary_rows)
    write_csv(data / "endpoint_amplitudes.csv", list(endpoint_rows[0]), endpoint_rows)
    return rows, summary_rows, endpoint_rows, cache


def log_binom(n: int, k: int):
    if k < 0 or k > n:
        return mp.ninf
    return mp.loggamma(n + 1) - mp.loggamma(k + 1) - mp.loggamma(n - k + 1)


def late_block(q: int, d: int, u: list[int], retained: int):
    """High-precision late block, retaining every finite-defect summand.

    Each returned coefficient is b_(N+1+j) R^j divided by the *leading*
    first coefficient u_m binom(aN-m,N+1-m). All d+1 sieve terms are
    evaluated; very small correction terms are not manually discarded.
    """
    size = 2 ** (q - 1)
    m = q + d
    k0 = size + 1 - m
    a, radius, _ = parameters(d)
    universes = [2 ** (m - h) - (m - h) for h in range(d + 1)]
    log_leading = mp.log(u[m]) + log_binom(universes[0], k0)
    log_c = log_leading + (size + 1) * mp.log(radius)
    summands = [mp.mpf(1)]
    for h in range(1, d + 1):
        log_summand = (mp.log(binom(k0 + h, h)) + mp.log(u[m - h])
                       + log_binom(universes[h], k0 + h) - log_leading)
        summands.append(mp.exp(log_summand))
    coefficients = []
    leading = mp.mpf(1)
    theta = radius * (universes[0] - k0) / (k0 + 1)
    assert 0 < theta < 1
    for j in range(min(retained, size)):
        coefficients.append(mp.fsum((-1) ** h * summands[h] for h in range(d + 1)))
        k = k0 + j
        for h in range(d + 1):
            summands[h] *= radius * (universes[h] - k - h) / (k + 1)
        leading *= radius * (universes[0] - k) / (k + 1)
    # The leading coefficient ratios decrease with j. Actual b_n is at most
    # its positive leading sieve term. This bounds the entire omitted
    # within-block tail for every |w| <= 1. It does not enclose roundoff.
    normalized_tail_bound = leading / (1 - theta) if retained < size else mp.mpf(0)
    return log_c, coefficients, normalized_tail_bound


def radial_tests(u: list[int], q_max: int, retained: int, data: Path):
    roots = [item for item in roots_of_unity() if item[0] in ("-1", "i", "exp(i*pi/4)")]
    ratio_rows, growth_rows = [], []
    worst_relative_tail = mp.mpf(0)
    for d in range(4):
        _, radius, rho = parameters(d)
        # Early blocks and the isolated n=1 term are evaluated directly,
        # including the finitely many exceptional zero-source conventions.
        early_n = 2 ** 9
        early = [mp.mpf(boundary_count(n, d, u)) * radius ** n
                 for n in range(1, early_n + 1)]
        blocks = []
        for q in range(10, q_max + 1):
            blocks.append((q, *late_block(q, d, u, retained)))
        for ell in range(8, 33):
            epsilon = mp.mpf(2) ** (-ell)
            r = mp.exp(-epsilon)
            real_sum = r * evaluate_polynomial(early, r)
            complex_sums = [r * root * evaluate_polynomial(early, r * root)
                            for _, _, _, root in roots]
            omitted_within_blocks = mp.mpf(0)
            for q, log_c, coefficients, tail in blocks:
                size = 2 ** (q - 1)
                amplitude = mp.exp(log_c - epsilon * (size + 1))
                real_sum += amplitude * evaluate_polynomial(coefficients, r)
                for index, (_, numerator, denominator, root) in enumerate(roots):
                    residue = (numerator * (size + 1)) % denominator
                    phase = mp.exp(2 * mp.pi * mp.j * residue / denominator)
                    complex_sums[index] += amplitude * phase * evaluate_polynomial(coefficients, r * root)
                omitted_within_blocks += amplitude * tail
            # For every q > q_max, theta_q <= 1/2 for these ranges. Also
            # c_q <= rho*u_(q+d) <= rho*2^((q+d)(q+d-1)/2).
            # Thus the q-tail is bounded by a geometric majorant whose
            # first term and ratio are explicit. No asymptotic substitution
            # for u_m or c_q is used in the numerical sum itself.
            q0 = q_max + 1
            m0 = q0 + d
            first_log = (mp.log(2 * rho) + mp.log(2) * m0 * (m0 - 1) / 2
                         - epsilon * (2 ** (q0 - 1) + 1))
            ratio_log = mp.log(2) * m0 - epsilon * 2 ** (q0 - 1)
            assert ratio_log < 0
            omitted_block_tail = mp.exp(first_log) / (1 - mp.exp(ratio_log))
            omission_bound = omitted_within_blocks + omitted_block_tail
            relative_omission = omission_bound / real_sum
            worst_relative_tail = max(worst_relative_tail, relative_omission)
            growth_rows.append({
                "d": d, "ell": ell, "epsilon": decimal(epsilon),
                "log10_B_positive": decimal(mp.log10(real_sum)),
                "relative_analytic_truncation_bound": decimal(relative_omission),
                "log10_omitted_late_blocks_bound": decimal(mp.log10(omitted_block_tail)),
            })
            for index, (name, _, _, root) in enumerate(roots):
                observed = complex_sums[index] / real_sum
                limit = root * (1 - rho) / (1 - rho * root)
                error = abs(observed - limit)
                ratio_rows.append({
                    "d": d, "ell": ell, "epsilon": decimal(epsilon), "zeta": name,
                    "ratio_real": decimal(observed.real), "ratio_imag": decimal(observed.imag),
                    "limit_real": decimal(limit.real), "limit_imag": decimal(limit.imag),
                    "absolute_error": decimal(error),
                    "analytic_ratio_truncation_bound": decimal(2 * relative_omission),
                })
        print(f"Radial blocks done: d={d}", flush=True)
    write_csv(data / "radial_ratios.csv", list(ratio_rows[0]), ratio_rows)
    write_csv(data / "radial_growth.csv", list(growth_rows[0]), growth_rows)
    return ratio_rows, growth_rows, worst_relative_tail


def precision_spot_check(u: list[int], q_max: int, retained: int, dps: int):
    """A separate higher-precision evaluation of the largest endpoint.

    This detects loss of significant digits in the cancellation of loggamma
    expressions. Agreement between two precisions is still not an interval
    certificate.
    """
    discrepancies = []
    for d in range(4):
        with mp.workdps(dps):
            low_log, low_coeff, _ = late_block(q_max, d, u, retained)
        with mp.workdps(dps + 40):
            high_log, high_coeff, _ = late_block(q_max, d, u, retained)
            discrepancies.append(abs(mp.exp(low_log - high_log) - 1))
            discrepancies.append(max(abs(x - y) for x, y in zip(low_coeff, high_coeff)))
    return max(discrepancies)


def make_figures(summary_rows, endpoint_rows, radial_rows, growth_rows, figures: Path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 9,
        "axes.titlesize": 10, "axes.labelsize": 9,
        "legend.fontsize": 8, "xtick.labelsize": 8, "ytick.labelsize": 8,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.edgecolor": "#687687", "axes.labelcolor": "#263345",
        "text.color": "#263345", "xtick.color": "#48576a", "ytick.color": "#48576a",
        "grid.color": "#dce3eb", "grid.linewidth": 0.6,
        "savefig.bbox": "tight", "pdf.fonttype": 42,
    })
    colors = ["#176a9b", "#d06821", "#278469", "#8757aa"]
    fig, axes = plt.subplots(1, 2, figsize=(7.1, 3.15), constrained_layout=True)
    for d, color in enumerate(colors):
        rows = [row for row in summary_rows if row["d"] == d]
        n = np.array([row["N"] for row in rows])
        bound = np.array([float(row["coefficient_l1_upper_bound"]) for row in rows])
        axes[0].plot(n, bound, "o-", color=color, lw=1.6, ms=3.4, label=f"$d={d}$")
        endpoint = [row for row in endpoint_rows if row["d"] == d]
        axes[1].plot(n, [float(row["relative_error"]) for row in endpoint],
                     "o-", color=color, lw=1.6, ms=3.4, label=f"$d={d}$")
    for axis in axes:
        axis.set_xscale("log", base=2)
        axis.set_yscale("log")
        axis.set_xlabel(r"Block size $N=2^{q-1}$")
        axis.grid(True, which="major")
        axis.set_axisbelow(True)
        axis.set_xticks([16, 64, 256, 1024], ["16", "64", "256", "1024"])
        axis.legend(frameon=False, ncol=2, loc="upper right")
    axes[0].set_title("(a) Uniform profile comparison", loc="left", pad=9)
    axes[0].set_ylabel(r"Coefficient bound for $\sup_{|w|\leq1}|P_q(w)-H_d(w)|$")
    axes[1].set_title("(b) Endpoint amplitude", loc="left", pad=9)
    axes[1].set_ylabel(r"$|c_q/c_q^{\rm asymp}-1|$")
    fig.savefig(figures / "profile_convergence.pdf")
    fig.savefig(figures / "profile_convergence.png", dpi=190)
    plt.close(fig)

    fig, axes = plt.subplots(1, 2, figsize=(7.1, 3.15), constrained_layout=True)
    labels = [("-1", r"$\zeta=-1$"), ("i", r"$\zeta=i$"),
              ("exp(i*pi/4)", r"$\zeta=e^{i\pi/4}$")]
    for (name, label), color in zip(labels, colors):
        rows = [row for row in radial_rows if row["d"] == 0 and row["zeta"] == name]
        axes[0].semilogy([row["ell"] for row in rows],
                         [float(row["absolute_error"]) for row in rows],
                         color=color, lw=1.7, label=label)
    for d, color in enumerate(colors):
        rows = [row for row in growth_rows if row["d"] == d]
        axes[1].plot([row["ell"] for row in rows],
                     [float(row["log10_B_positive"]) for row in rows],
                     color=color, lw=1.7, label=f"$d={d}$")
    for axis in axes:
        axis.set_xlabel(r"Approach parameter $\ell$ in $r=\exp(-2^{-\ell})$")
        axis.set_xticks([8, 12, 16, 20, 24, 28, 32])
        axis.grid(True, which="major")
        axis.set_axisbelow(True)
        axis.legend(frameon=False, loc="best")
    axes[0].set_title("(a) Dyadic radial ratios, $d=0$", loc="left", pad=9)
    axes[0].set_ylabel("Absolute difference from the limiting ratio")
    axes[1].set_title("(b) Divergence on the positive radius", loc="left", pad=9)
    axes[1].set_ylabel(r"$\log_{10} B_d(R_d r)$")
    fig.savefig(figures / "radial_behavior.pdf")
    fig.savefig(figures / "radial_behavior.png", dpi=190)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=64)
    parser.add_argument("--brute-n", type=int, default=7)
    parser.add_argument("--profile-q-min", type=int, default=5)
    parser.add_argument("--profile-q-max", type=int, default=11)
    parser.add_argument("--radial-q-max", type=int, default=60)
    parser.add_argument("--radial-terms", type=int, default=128)
    parser.add_argument("--dps", type=int, default=100)
    parser.add_argument("--no-figures", action="store_true")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    if not 1 <= args.brute_n <= 7:
        parser.error("--brute-n must be in 1,...,7; exhaustive growth is exponential")
    if args.max_n < args.brute_n or args.radial_q_max < 40:
        parser.error("need max-n >= brute-n and radial-q-max >= 40")
    mp.mp.dps = args.dps
    # Python's safety limit on decimal conversion does not affect the exact
    # calculations, but lifted limits keep larger optional CSV runs possible.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    data = args.out_dir / "data"
    figures = args.out_dir / "figures"
    data.mkdir(parents=True, exist_ok=True)
    figures.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    core_max = max(args.max_n, args.radial_q_max + 3, args.profile_q_max + 3, 10)
    u = total_counts(core_max)
    triangle, divisions = source_deletion_triangle(args.max_n)
    cells = covering_checks = finite_defect_checks = support_checks = 0
    triangle_rows = []
    for n in range(1, args.max_n + 1):
        assert sum(triangle[n]) == u[n]
        maximum = n - dyadic_index(n)
        for k in range(1, n + 1):
            assert triangle[n][k] == source_sieve(n, k, u), (n, k)
            cells += 1
            assert (triangle[n][k] > 0) == (k <= maximum), (n, k)
            support_checks += 1
            m = n - k
            leading = u[m] * binom(2 ** m - m, k)
            deficit = leading - triangle[n][k]
            assert deficit >= 0 and (1 << k) * deficit <= m * leading
            covering_checks += 1
            triangle_rows.append({"n": n, "k": k, "u_n_k": triangle[n][k]})
        for d in range(4):
            k = n - dyadic_index(n) - d
            if k >= 1:
                assert boundary_count(n, d, u) == triangle[n][k]
                finite_defect_checks += 1
    core_bound_checks = 0
    core_rows = []
    for m in range(1, core_max + 1):
        lower = 2 ** ((m - 1) * (m - 2) // 2)
        upper = 2 ** (m * (m - 1) // 2)
        assert lower <= u[m] <= upper
        core_bound_checks += 1
        core_rows.append({"m": m, "u_m": u[m], "lower_bound": lower, "upper_bound": upper})
    exhaustive = full_set_counts(args.brute_n)
    for item in exhaustive:
        n = item["n"]
        assert item["full_sets"] == u[n]
        assert item["source_row"] == triangle[n]
    boundary_rows = []
    for n in range(1, 129):
        for d in range(4):
            q = dyadic_index(n)
            boundary_rows.append({"n": n, "q": q, "d": d, "m": q + d,
                                  "k": n - q - d, "b_n_d": boundary_count(n, d, u)})
    write_csv(data / "source_triangle.csv", list(triangle_rows[0]), triangle_rows)
    write_csv(data / "core_counts.csv", list(core_rows[0]), core_rows)
    write_csv(data / "boundary_counts.csv", list(boundary_rows[0]), boundary_rows)
    write_csv(data / "exhaustive_counts.csv", ["n", "full_sets", "attempted_extensions", "source_row"],
              [{**item, "attempted_extensions": item.get("attempted_extensions", 0),
                "source_row": ";".join(map(str, item["source_row"]))} for item in exhaustive])
    print(f"Exact checks passed: {cells} triangle cells; full sets through {args.brute_n}.", flush=True)
    profiles, profile_summary, endpoints, _ = finite_profile_tests(
        args.profile_q_min, args.profile_q_max, u, data)
    print(f"Exact-coefficient block profiles evaluated: {len(profiles)} point tests.", flush=True)
    radial, growth, radial_tail = radial_tests(u, args.radial_q_max, args.radial_terms, data)
    precision_error = precision_spot_check(u, args.radial_q_max, args.radial_terms, args.dps)
    if not args.no_figures:
        make_figures(profile_summary, endpoints, radial, growth, figures)
    report = {
        "status": "all exact assertions passed",
        "python": platform.python_version(), "mpmath": mp.__version__,
        "working_decimal_digits": args.dps,
        "triangle_max_n": args.max_n, "triangle_cells_compared": cells,
        "source_deletion_divisibility_checks": divisions,
        "source_support_checks": support_checks,
        "covering_inequalities_checked_exactly": covering_checks,
        "finite_defect_entries_compared": finite_defect_checks,
        "core_bounds_checked_for_m_1_through": core_bound_checks,
        "exhaustive_nested_frozenset_generation": exhaustive,
        "boundary_table_rows": len(boundary_rows),
        "profile_q_range": [args.profile_q_min, args.profile_q_max],
        "profile_complex_point_tests": len(profiles),
        "profile_direct_binomial_spot_checks": 16 * (args.profile_q_max - args.profile_q_min + 1),
        "profile_max_l1_bound_times_N_over_m": decimal(max(
            mp.mpf(row["l1_bound_times_N_over_m"]) for row in profile_summary)),
        "profile_errors_at_largest_q": [row for row in profile_summary
                                       if row["q"] == args.profile_q_max],
        "radial_q_max": args.radial_q_max, "radial_terms_per_late_block": args.radial_terms,
        "radial_ratio_tests": len(radial),
        "maximum_relative_analytic_radial_truncation_bound": decimal(radial_tail),
        "endpoint_precision_comparison_digits": [args.dps, args.dps + 40],
        "largest_endpoint_precision_disagreement": decimal(precision_error),
        "radial_errors_at_ell_32": [row for row in radial if row["ell"] == 32],
        "proof_status": "Exact finite tests and non-interval numerical evidence only; the article's proofs establish infinite statements.",
        "truncation_status": "Analytic bounds cover omitted terms; floating-point rounding is not enclosed by interval arithmetic.",
        "elapsed_seconds": round(time.perf_counter() - start, 3),
    }
    (data / "validation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
