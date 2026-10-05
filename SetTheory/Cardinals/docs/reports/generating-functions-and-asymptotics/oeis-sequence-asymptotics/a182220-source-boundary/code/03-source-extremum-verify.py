#!/usr/bin/env python3
"""Reproducible checks and numerical diagnostics for dyadic source boundaries.

All enumeration and inequalities in ``exact_checks`` use Python integers.
The two source triangles are constructed independently.  Brute enumeration
uses neither recurrence.  The block and radial diagnostics use mpmath; they
are not interval-certified and are not substitutes for the proofs.

Usage: python verify.py --max-n 64 --brute-n 6
Requires Python 3.10+, mpmath, matplotlib; no network access is used.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import sys
import time

import mpmath as mp


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
FIGURES = ROOT / "figures"


def choose(n: int, k: int) -> int:
    return math.comb(n, k) if n >= 0 and 0 <= k <= n else 0


def dyadic_q(n: int) -> int:
    """ceil(log_2(n)), without a floating-point logarithm."""
    if n < 1:
        raise ValueError("n must be positive")
    return (n - 1).bit_length()


def marked_source_triangle(max_n: int) -> tuple[list[int], list[list[int]]]:
    """Total recurrence followed by the marked-source binomial sieve."""
    totals = [1]
    for n in range(1, max_n + 1):
        totals.append(sum(
            (-1) ** (n - m - 1) * choose((1 << m) - m, n - m) * totals[m]
            for m in range(n)
        ))
    rows = [[1]]
    for n in range(1, max_n + 1):
        row = [0]
        for s in range(1, n + 1):
            row.append(sum(
                (-1) ** (t - s) * choose(t, s) * totals[n - t]
                * choose((1 << (n - t)) - (n - t), t)
                for t in range(s, n + 1)
            ))
        rows.append(row)
    return totals, rows


def deletion_triangle(max_n: int) -> tuple[list[list[int]], int]:
    """Source-deletion recurrence; it does not read the other construction."""
    rows = [[1]]
    divisions = 0
    for n in range(1, max_n + 1):
        previous = rows[-1]
        row = [0] * (n + 1)
        for s in range(1, n + 1):
            numerator = ((1 << (n - s)) - (n - 1)) * previous[s - 1]
            numerator += sum(
                choose(s + j, j + 1) * (1 << (n - 1 - s - j))
                * previous[s + j]
                for j in range(n - s)
            )
            assert numerator % s == 0, (n, s, "nonintegral deletion recurrence")
            row[s] = numerator // s
            divisions += 1
        rows.append(row)
    return rows, divisions


def finite_defect(n: int, d: int, totals: list[int]) -> int:
    q = dyadic_q(n)
    m = q + d
    k = n - m
    if k < 1:
        return 0
    return sum(
        (-1) ** h * choose(k + h, h) * totals[m - h]
        * choose((1 << (m - h)) - (m - h), k + h)
        for h in range(d + 1)
    )


def brute_classes(n: int) -> dict[str, object]:
    """All topologically labeled DAGs, collapsed to nested finite sets."""
    classes: dict[frozenset, int] = {}
    surviving = 0
    for masks in itertools.product(*(range(1 << v) for v in range(n))):
        if len(set(masks)) != n:
            continue
        surviving += 1
        codes: list[frozenset] = []
        targeted = 0
        for v, mask in enumerate(masks):
            codes.append(frozenset(codes[w] for w in range(v) if mask >> w & 1))
            targeted |= mask
        assert len(set(codes)) == n
        canonical = frozenset(codes)
        sources = n - targeted.bit_count()
        if canonical in classes:
            assert classes[canonical] == sources
        classes[canonical] = sources
    row = [0] * (n + 1)
    for sources in classes.values():
        row[sources] += 1
    return {
        "n": n,
        "all_topological_graphs": 1 << (n * (n - 1) // 2),
        "extensional_topological_graphs": surviving,
        "isomorphism_classes": len(classes),
        "source_row": row,
    }


def exact_checks(max_n: int, brute_n: int) -> tuple[list[int], dict[str, object]]:
    totals, marked = marked_source_triangle(max_n)
    deletion, divisions = deletion_triangle(max_n)
    assert marked == deletion
    cells = support_checks = covering_checks = sharp_covering_checks = 0
    defect_checks = extremizer_checks = core_checks = marked_moment_checks = 0
    for n in range(1, max_n + 1):
        assert sum(marked[n]) == totals[n]
        assert totals[n] == sum(deletion[n])
        q = dyadic_q(n)
        assert (1 << ((n - 1) * (n - 2) // 2)) <= totals[n]
        assert totals[n] <= (1 << (n * (n - 1) // 2))
        core_checks += 1
        for s in range(1, n + 1):
            value = marked[n][s]
            assert value >= 0
            assert (value > 0) == (s <= n - q)
            support_checks += 1
            cells += 1
            m = n - s
            leading = totals[m] * choose((1 << m) - m, s)
            deficit = leading - value
            assert deficit >= 0
            assert (deficit << s) <= m * leading
            covering_checks += 1
            if m >= 1:
                source_sum = sum(j * marked[m][j] for j in range(m + 1))
                assert deficit <= source_sum * choose((1 << (m - 1)) - m, s)
                sharp_covering_checks += 1
        exact_boundary = totals[q] * choose((1 << q) - q, n - q)
        assert marked[n][n - q] == exact_boundary
        extremizer_checks += 1
        for d in range(4):
            k = n - q - d
            if k >= 1:
                assert finite_defect(n, d, totals) == marked[n][k]
                defect_checks += 1
        source_sum = sum(s * marked[n][s] for s in range(n + 1))
        assert source_sum == ((1 << (n - 1)) - n + 1) * totals[n - 1]
        marked_moment_checks += 1
    brute = []
    for n in range(1, brute_n + 1):
        result = brute_classes(n)
        assert result["source_row"] == marked[n]
        brute.append(result)
    with (DATA / "source_triangle.csv").open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["n", "sources", "unlabeled_count"])
        for n, row in enumerate(marked):
            for s, value in enumerate(row):
                writer.writerow([n, s, value])
    with (DATA / "core_counts.csv").open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["m", "U_m_A001192", "chain_lower_bound", "topological_upper_bound"])
        for m, total in enumerate(totals):
            lower = 1 if m == 0 else 1 << ((m - 1) * (m - 2) // 2)
            writer.writerow([m, total, lower, 1 << (m * (m - 1) // 2)])
    summary = {
        "status": "PASS",
        "integer_arithmetic": True,
        "max_n": max_n,
        "independently_matching_triangle_cells": cells,
        "exact_divisibility_checks": divisions,
        "support_checks": support_checks,
        "general_covering_checks": covering_checks,
        "sharp_covering_checks": sharp_covering_checks,
        "extremizer_formula_checks": extremizer_checks,
        "finite_defect_checks_d_0_through_3": defect_checks,
        "two_sided_core_bound_checks": core_checks,
        "marked_first_moment_checks": marked_moment_checks,
        "brute_enumeration": brute,
        "initial_U_m": totals[:17],
    }
    return totals, summary


def parameters(d: int) -> tuple[int, int, mp.mpf]:
    c = 1 << (d + 1)
    a = c - 1
    radius = mp.mpf(a) ** a / mp.mpf(c) ** c
    return c, a, radius


def mpstr(value: mp.mpf | mp.mpc, digits: int = 24) -> str:
    return mp.nstr(value, digits)


def log10_or_inf(value: mp.mpf) -> str:
    return "-inf" if value == 0 else mpstr(mp.log10(value))


def exact_block_prefix(q: int, d: int, totals: list[int], length: int = 200):
    """Exact integers, using the (d+1)-term formula and exact term updates."""
    K = 1 << (q - 1)
    m = q + d
    start = max(K + 1, m + 1)
    if start > 2 * K:
        return None
    k0 = start - m
    terms = [
        choose(k0 + h, h) * totals[m - h]
        * choose((1 << (m - h)) - (m - h), k0 + h)
        for h in range(d + 1)
    ]
    values = []
    for j in range(min(length, 2 * K - start + 1)):
        value = sum((-1) ** h * term for h, term in enumerate(terms))
        assert value > 0
        values.append(value)
        k = k0 + j
        for h in range(d + 1):
            factor = (1 << (m - h)) - (m - h) - k - h
            numerator = terms[h] * max(0, factor)
            assert numerator % (k + 1) == 0
            terms[h] = numerator // (k + 1)
    return start, k0, values


def block_diagnostics(totals: list[int]) -> list[dict[str, object]]:
    rows = []
    for d in range(3):
        c, a, radius = parameters(d)
        target = 1 / (1 - a * radius)
        for q in (5, 8, 11, 14):
            K = 1 << (q - 1)
            m = q + d
            start, k0, values = exact_block_prefix(q, d, totals)
            assert start == K + 1
            b0 = values[0]
            profile = sum(mp.mpf(v) / b0 * radius ** j for j, v in enumerate(values))
            leading0 = totals[m] * choose(c * K - m, k0)
            theta = mp.mpf(c * K - m - k0) / (k0 + 1) * radius
            assert theta < 1
            tail = mp.mpf(0)
            if len(values) < K:
                tail = mp.mpf(leading0) / b0 * theta ** len(values) / (1 - theta)
            logarithm_A = mp.log(b0) + start * mp.log(radius)
            cover = mp.mpf(m) * mp.power(2, -k0)
            rows.append({
                "q": q, "d": d, "K": K, "core_size_m": m,
                "radius_R": mpstr(radius), "a": a,
                "Q_q_at_R_numerical": mpstr(profile),
                "limit_1_over_1_minus_aR": mpstr(target),
                "absolute_difference": mpstr(abs(profile - target)),
                "log_A_q": mpstr(logarithm_A),
                "quadratic_remainder_divided_by_q": mpstr(
                    (logarithm_A - mp.log(2) * q * q / 2) / q),
                "exact_prefix_length": len(values),
                "log10_omitted_profile_tail_upper_bound": log10_or_inf(tail),
                "log10_general_covering_relative_bound": log10_or_inf(cover),
            })
    with (DATA / "block_profiles.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def first_correction_checks(totals: list[int]) -> dict[str, object]:
    """Independent first-order product expansions and numerical residuals.

    The exact checks multiply truncated formal products instead of using
    the proposed rational-function correction.  The diagnostics evaluate
    actual finite-defect coefficients, normalized by the Boolean leading
    coefficient, and an independent log-gamma binomial evaluation.
    """
    profile_coefficient_checks = amplitude_coefficient_checks = 0
    for c in (2, 4, 8, 16):
        a = c - 1
        for m in range(1, 21):
            # A pair (constant, linear) represents a polynomial modulo t^2,
            # where t=1/K. Each factor is
            # (a-(h+1)t)/(1+(2-m+h)t).
            constant, linear = 1, 0
            for j in range(13):
                predicted = ((m - 1) * j * a ** j
                             - c * a ** (j - 1) * j * (j + 1) // 2) if j else 0
                assert constant == a ** j
                assert linear == predicted
                profile_coefficient_checks += 1
                factor_linear = -(j + 1) - a * (2 - m + j)
                constant, linear = constant * a, linear * a + constant * factor_linear

            # Exact factorization of the shifted binomial coefficient:
            # C(cK-m,K+1-m)/C(cK,K)=(K)_(m-1)*aK/(cK)_m.
            product_constant, product_linear = Fraction(1), Fraction(0)
            for h in range(m - 1):
                product_linear -= product_constant * h
            for h in range(m):
                product_linear += product_constant * Fraction(h, c)
            stirling_linear = (Fraction(1, c) - 1 - Fraction(1, a)) / 12
            independently_expanded = product_linear + stirling_linear
            predicted_E = ((m - 1) - Fraction(a * m * (m - 1), 2 * c)
                           + (Fraction(1, c) - 1 - Fraction(1, a)) / 12)
            assert independently_expanded == predicted_E
            amplitude_coefficient_checks += 1

    rows = []
    for d in range(3):
        c, a, radius = parameters(d)
        circle_radius = (radius + mp.mpf(1) / a) / 2
        for q in (5, 8, 11, 14):
            K = 1 << (q - 1)
            m = q + d
            start, k0, values = exact_block_prefix(q, d, totals)
            assert start == K + 1
            leading0 = totals[m] * choose(c * K - m, k0)
            coefficient_prefix = [mp.mpf(value) / leading0 for value in values]

            def profile_remainder(z):
                observed = mp.polyval(list(reversed(coefficient_prefix)), z)
                zeroth = 1 / (1 - a * z)
                first = ((m - 1) * a * z / (1 - a * z) ** 2
                         - c * z / (1 - a * z) ** 3)
                return observed - zeroth - first / K

            at_radius = abs(profile_remainder(radius))
            sampled_maximum = max(abs(profile_remainder(
                circle_radius * mp.exp(2j * mp.pi * h / 64))) for h in range(64))
            theta = mp.mpf(c * K - m - k0) / (k0 + 1) * circle_radius
            assert theta < 1
            circle_tail = (theta ** len(values) / (1 - theta)
                           if len(values) < K else mp.mpf(0))
            E = ((m - 1) - mp.mpf(a * m * (m - 1)) / (2 * c)
                 + (mp.mpf(1) / c - 1 - mp.mpf(1) / a) / 12)
            log_binomial = (mp.loggamma(c * K - m + 1) - mp.loggamma(k0 + 1)
                            - mp.loggamma(a * K))
            log_amplitude_ratio = (log_binomial + K * mp.log(radius) + m * mp.log(c)
                                   - mp.log(mp.mpf(c * a) / (2 * mp.pi * K)) / 2)
            amplitude_ratio = mp.exp(log_amplitude_ratio)
            amplitude_error = abs(amplitude_ratio - 1 - E / K)
            rows.append({
                "d": d, "q": q, "K": K, "m": m,
                "profile_normalization": "U_m times binom(cK-m,K+1-m), not actual b_(K+1)",
                "profile_first_correction_abs_error_at_R": mpstr(at_radius),
                "profile_error_at_R_times_K2_over_m2": mpstr(at_radius * K * K / (m * m)),
                "sampled_circle_radius": mpstr(circle_radius),
                "sampled_circle_points": 64,
                "sampled_max_profile_first_correction_abs_error": mpstr(sampled_maximum),
                "sampled_max_error_times_K2_over_m2": mpstr(sampled_maximum * K * K / (m * m)),
                "log10_uniform_circle_omitted_prefix_tail_majorant": log10_or_inf(circle_tail),
                "amplitude_ratio_to_leading_term": mpstr(amplitude_ratio),
                "predicted_amplitude_E": mpstr(E),
                "amplitude_first_correction_abs_error": mpstr(amplitude_error),
                "amplitude_error_times_K2_over_m4": mpstr(amplitude_error * K * K / (m ** 4)),
                "arithmetic_certification": "100-digit mpmath; not interval-certified",
            })
    with (DATA / "first_correction_checks.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    return {
        "exact_profile_first_order_coefficient_checks": profile_coefficient_checks,
        "exact_amplitude_first_order_coefficient_checks": amplitude_coefficient_checks,
        "exact_check_parameters": "c in {2,4,8,16}; 1<=m<=20; profile coefficients 0<=j<=12",
        "numerical_residuals": rows,
        "sampling_caveat": "A maximum over 64 circle samples is not a bound for the full circle.",
    }


def write_latex_tables(blocks, radial, corrections) -> None:
    """Generate manuscript-ready tables whenever the diagnostic script runs."""
    def fixed(value, digits=10):
        return f"{float(value):.{digits}f}"

    def scientific(value):
        mantissa, exponent = f"{float(value):.6e}".split("e")
        return mantissa + r"\times10^{" + str(int(exponent)) + "}"

    lines = [
        "% Generated by verify.py. Numerical values are not interval-certified.",
        r"\begin{table}[htbp]", r"\centering",
        r"\caption{Numerical block profiles $Q_q(R_d)$, with $Q_q=P_q/P_q(0)$",
        r"normalized by the actual first coefficient $b_{K+1}^{(d)}$.",
        r"The final row gives $1/(1-a_dR_d)$.",
        r"Retained coefficients are exact integers; evaluations are numerical.}",
        r"\label{tab:computed-block-profiles}",
        r"\begin{tabular}{rrrr}", r"\toprule",
        r"$q$ & $d=0$ & $d=1$ & $d=2$ \\", r"\midrule",
    ]
    for q in (5, 8, 11, 14):
        entries = [next(row for row in blocks if row["q"] == q and row["d"] == d)
                   for d in range(3)]
        lines.append(str(q) + " & " + " & ".join(
            fixed(row["Q_q_at_R_numerical"]) for row in entries) + r" \\")
    entries = [next(row for row in blocks if row["d"] == d) for d in range(3)]
    lines += [r"\midrule", r"$\infty$ & " + " & ".join(
        fixed(row["limit_1_over_1_minus_aR"]) for row in entries) + r" \\",
        r"\bottomrule", r"\end{tabular}", r"\end{table}", "",
        r"\begin{table}[htbp]", r"\centering",
        r"\caption{Absolute errors in the numerical radial-ratio limit",
        r"\eqref{eq:phase-main} at $r=0.9999$.",
        r"Large blocks use the covering proxy with analytic truncation and covering",
        r"majorants. Floating-point roundoff is not interval-certified.}",
        r"\label{tab:computed-radial-errors}",
        r"\begin{tabular}{lrrr}",
    ]
    lines += [r"\toprule", r"$\zeta$ & $d=0$ & $d=1$ & $d=2$ \\", r"\midrule"]
    for order, label in ((4, r"$i$"), (8, r"$e^{\pi i/4}$")):
        entries = [next(row for row in radial if row["root_order"] == order
                        and row["d"] == d and row["r"] == "0.9999") for d in range(3)]
        lines.append(label + " & " + " & ".join(
            "$" + scientific(row["absolute_difference_from_limit"]) + "$"
            for row in entries) + r" \\")
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]
    (DATA / "diagnostic_tables.tex").write_text("\n".join(lines))

    lines = [
        "% Generated by verify.py. Optional appendix table; numerical diagnostics only.",
        r"\begin{table}[htbp]", r"\centering",
        r"\caption{First-order correction diagnostics at $z=R_d$.",
        r"$\varepsilon_P$ is the absolute remainder after the displayed first correction",
        r"to the proxy-normalized profile $P_q$; $\varepsilon_A$ is the absolute",
        r"remainder after $1+E/K$ in the normalized proxy amplitude.",
        r"The scalings illustrate the predicted orders; they are not proofs or interval certificates.}",
        r"\label{tab:computed-first-corrections}",
        r"\begin{tabular}{rrrr}", r"\toprule",
        r"$d$ & $q$ & $(K^2/m^2)\varepsilon_P$ & $(K^2/m^4)\varepsilon_A$ \\",
        r"\midrule",
    ]
    for row in corrections["numerical_residuals"]:
        if row["q"] >= 8:
            lines.append(f"{row['d']} & {row['q']} & "
                         + fixed(row["profile_error_at_R_times_K2_over_m2"], 7) + " & "
                         + fixed(row["amplitude_error_times_K2_over_m4"], 7) + r" \\")
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]
    (DATA / "first_correction_tables.tex").write_text("\n".join(lines))


def radial_block(q: int, d: int, totals: list[int], x: mp.mpf,
                 zeta: mp.mpc, prefix_length: int = 220):
    """Return a scaled block and explicit analytic error majorants.

    At q <= 11 the retained coefficient prefix is exact. At q >= 12 it
    is the Boolean covering proxy U_m binom(2^m-m,n-m). The discrepancy
    is bounded coefficientwise by m*2^(-(n-m)) times that proxy.
    """
    K = 1 << (q - 1)
    m = q + d
    start = max(K + 1, m + 1)
    if start > 2 * K:
        return None
    k0 = start - m
    M = (1 << m) - m
    theta = mp.mpf(M - k0) / (k0 + 1) * x
    assert theta < 1, (q, d, theta)
    length = min(prefix_length, 2 * K - start + 1)
    exact = q <= 11
    if exact:
        _, _, values = exact_block_prefix(q, d, totals, prefix_length)
        base = values[0]
        ratios = [mp.mpf(value) / base for value in values]
        log_weight = mp.log(base) + start * mp.log(x)
        leading_over_base = mp.mpf(totals[m] * choose(M, k0)) / base
    else:
        log_binomial = mp.loggamma(M + 1) - mp.loggamma(k0 + 1) - mp.loggamma(M - k0 + 1)
        log_weight = mp.log(totals[m]) + log_binomial + start * mp.log(x)
        ratios = [mp.mpf(1)]
        for j in range(1, length):
            ratios.append(ratios[-1] * (M - k0 - j + 1) / (k0 + j))
        leading_over_base = mp.mpf(1)
    positive_profile = sum(value * x ** j for j, value in enumerate(ratios))
    complex_profile = zeta ** start * sum(
        value * (x * zeta) ** j for j, value in enumerate(ratios))
    omitted = mp.mpf(0)
    if length < 2 * K - start + 1:
        omitted = leading_over_base * theta ** length / (1 - theta)
    covering = mp.mpf(0) if exact else mp.mpf(m) * mp.power(2, -k0) / (1 - theta)
    return log_weight, positive_profile, complex_profile, omitted, covering


def radial_diagnostics(totals: list[int]) -> list[dict[str, object]]:
    qmax = 24
    rows = []
    for d in range(3):
        _, a, radius = parameters(d)
        for order in (4, 8):
            zeta = mp.exp(2j * mp.pi / order)
            target = zeta * (1 - a * radius) / (1 - a * radius * zeta)
            for r_text in ("0.9", "0.99", "0.999", "0.9999"):
                r = mp.mpf(r_text)
                x = radius * r
                blocks = [radial_block(q, d, totals, x, zeta)
                          for q in range(1, qmax + 1)]
                blocks = [block for block in blocks if block is not None]
                # The q=0 singleton n=1 contributes only at defect d=0.
                if d == 0:
                    blocks.append((mp.log(x), mp.mpf(1), zeta, mp.mpf(0), mp.mpf(0)))
                scale = max(block[0] for block in blocks)
                denominator = sum(mp.exp(L - scale) * p for L, p, _, _, _ in blocks)
                numerator = sum(mp.exp(L - scale) * p for L, _, p, _, _ in blocks)
                prefix_error = sum(mp.exp(L - scale) * e for L, _, _, e, _ in blocks)
                covering_error = sum(mp.exp(L - scale) * e for L, _, _, _, e in blocks)
                # For q >= qmax+1, m <= K/2 and the within-block ratio
                # is <= 2a. For the binomial estimate put k0=K+1-m.
                # Since k0<=K<=cK/2 and m>=1,
                # C(cK-m,k0)<=C(cK,k0)<=C(cK,K).
                # Finally C(cK,K)*(1/a)^K <= (1+1/a)^(cK)
                # gives C(cK,K)<=R^(-K), with R=a^a/c^c.
                # Thus block <= Rr/(1-2aR) * 2^(m(m-1)/2) r^K.
                q0 = qmax + 1
                K0 = 1 << (q0 - 1)
                m0 = q0 + d
                assert m0 <= K0 // 2
                tail_ratio = mp.power(2, q0 + d) * r ** K0
                assert tail_ratio < 1
                log_first_tail = (
                    mp.log(x / (1 - 2 * a * radius))
                    + mp.log(2) * m0 * (m0 - 1) / 2 + K0 * mp.log(r)
                )
                uncomputed_block_error = mp.exp(log_first_tail - scale) / (1 - tail_ratio)
                total_error = prefix_error + covering_error + uncomputed_block_error
                assert total_error < denominator
                ratio = numerator / denominator
                ratio_error_majorant = 2 * total_error / (denominator - total_error)
                rows.append({
                    "d": d, "root_order": order, "r": r_text,
                    "ratio_real": mpstr(mp.re(ratio)),
                    "ratio_imaginary": mpstr(mp.im(ratio)),
                    "limit_real": mpstr(mp.re(target)),
                    "limit_imaginary": mpstr(mp.im(target)),
                    "absolute_difference_from_limit": mpstr(abs(ratio - target)),
                    "largest_included_dyadic_q": qmax,
                    "exact_coefficients_through_block_q": 11,
                    "covering_proxy_from_block_q": 12,
                    "log10_ratio_error_analytic_majorant": log10_or_inf(ratio_error_majorant),
                    "log10_prefix_tail_relative_majorant": log10_or_inf(prefix_error / denominator),
                    "log10_covering_relative_majorant": log10_or_inf(covering_error / denominator),
                    "log10_uncomputed_blocks_relative_majorant": log10_or_inf(uncomputed_block_error / denominator),
                    "log_B_d_Rr_numerical": mpstr(scale + mp.log(denominator)),
                    "arithmetic_certification": "100-digit mpmath; not interval-certified",
                })
    with (DATA / "radial_ratios.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def scientific_figures(totals: list[int], radial_rows: list[dict[str, object]]) -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import MaxNLocator

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 10,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.labelcolor": "#25354a", "text.color": "#25354a",
        "xtick.color": "#44546a", "ytick.color": "#44546a",
        "axes.titleweight": "semibold", "figure.dpi": 150,
        "savefig.dpi": 200, "pdf.fonttype": 42,
    })
    xs = list(range(1, 257))
    ys = [math.log(finite_defect(n, 0, totals)) - n * math.log(4) for n in xs]
    with (DATA / "extremal_scaled_coefficients.csv").open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["n", "q", "b_n_d0_exact", "natural_log_b_n_R_power_n"])
        for n, y in zip(xs, ys):
            writer.writerow([n, dyadic_q(n), finite_defect(n, 0, totals), format(y, ".16g")])
    fig, ax = plt.subplots(figsize=(8.6, 4.9), constrained_layout=True)
    ax.plot(xs, ys, color="#156c91", linewidth=1.7)
    powers = [2 ** q for q in range(2, 9)]
    for power in powers:
        ax.axvline(power, color="#c7d0d9", linewidth=0.7, zorder=0)
    starts = [2 ** q + 1 for q in range(2, 8)]
    ax.scatter(starts, [ys[n - 1] for n in starts], s=29, color="#bf5b39", zorder=4,
               label="First coefficient after a power of two")
    ax.axhline(0, color="#748295", linewidth=0.7, linestyle="--")
    ax.set(xlabel=r"Coefficient index $n$", ylabel=r"$\log\!\left(b_n^{(0)}4^{-n}\right)$",
           xlim=(0, 260), title="Dyadic resets in the extremal source counts")
    ax.set_xticks([0, 32, 64, 96, 128, 160, 192, 224, 256])
    ax.yaxis.set_major_locator(MaxNLocator(6))
    ax.grid(axis="y", color="#e6ebef", linewidth=0.65)
    ax.legend(loc="lower left", frameon=False, fontsize=9)
    fig.savefig(FIGURES / "dyadic_scaled_coefficients.pdf")
    fig.savefig(FIGURES / "dyadic_scaled_coefficients.png")
    plt.close(fig)

    fig, axes = plt.subplots(1, 2, figsize=(9.1, 4.3), constrained_layout=True)
    colors = ["#156c91", "#bf5b39", "#5b7e3e"]
    for ax, order in zip(axes, (4, 8)):
        for d, color in enumerate(colors):
            selected = [row for row in radial_rows if row["d"] == d and row["root_order"] == order]
            xx = [1 - float(row["r"]) for row in selected]
            yy = [float(row["absolute_difference_from_limit"]) for row in selected]
            ax.loglog(xx, yy, "o-", color=color, label=f"Defect d = {d}", linewidth=1.5, markersize=4.5)
        ax.invert_xaxis()
        ax.set(xlabel=r"Distance to the circle, $1-r$",
               title=r"$\zeta=i$" if order == 4 else r"$\zeta=e^{\pi i/4}$")
        ax.grid(which="major", color="#e3e9ee", linewidth=0.7)
        ax.legend(frameon=False, fontsize=8.8)
    axes[0].set_ylabel("Absolute error from the radial-ratio limit")
    fig.suptitle("Numerical radial phase convergence", fontsize=13, fontweight="semibold")
    fig.savefig(FIGURES / "radial_phase_convergence.pdf")
    fig.savefig(FIGURES / "radial_phase_convergence.png")
    plt.close(fig)


def write_summary(exact, blocks, radial, corrections, elapsed: float) -> None:
    result = {
        "exact_verification": exact,
        "block_diagnostics": blocks,
        "radial_diagnostics": radial,
        "first_correction_checks": corrections,
        "numerical_caveat": (
            "Diagnostics use 100-digit mpmath, not interval arithmetic. "
            "Analytic truncation and covering error bounds do not certify floating-point roundoff. "
            "The finite computations do not prove infinite asymptotic or natural-boundary statements."
        ),
        "elapsed_seconds": elapsed,
    }
    (DATA / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    lines = [
        "OEIS SOURCE-BOUNDARY VERIFICATION",
        "================================",
        "",
        "EXACT INTEGER CHECKS: PASS",
        f"Two independently constructed source triangles agree through n={exact['max_n']}.",
    ]
    for key, value in exact.items():
        if key not in {"brute_enumeration", "initial_U_m", "status", "integer_arithmetic", "max_n"}:
            lines.append(f"  {key}: {value}")
    lines += ["", "Independent enumeration of all topologically labeled DAGs:",
              "n    all graphs    extensional graphs    isomorphism classes    source row"]
    for row in exact["brute_enumeration"]:
        lines.append(f"{row['n']:<5}{row['all_topological_graphs']:<14}"
                     f"{row['extensional_topological_graphs']:<22}"
                     f"{row['isomorphism_classes']:<23}{row['source_row'][1:]}")
    lines += ["", "BLOCK PROFILES (exact integer coefficient prefixes, numerical evaluation):",
              "d  q     Q_q(R)                limiting value           absolute difference"]
    for row in blocks:
        lines.append(f"{row['d']}  {row['q']:<5}"
                     f"{float(row['Q_q_at_R_numerical']):<22.14g}"
                     f"{float(row['limit_1_over_1_minus_aR']):<25.14g}"
                     f"{float(row['absolute_difference']):.9g}")
    lines += ["", "RADIAL RATIOS (numerical, with analytic truncation/covering majorants):",
              "d  order   r       ratio real          ratio imaginary     error from limit"]
    for row in radial:
        lines.append(f"{row['d']}  {row['root_order']:<7}{row['r']:<8}"
                     f"{float(row['ratio_real']):<20.11g}"
                     f"{float(row['ratio_imaginary']):<20.11g}"
                     f"{float(row['absolute_difference_from_limit']):.8g}")
    lines += [
        "", "FIRST-ORDER CORRECTIONS",
        f"Exact coefficient checks from independent truncated products: {corrections['exact_profile_first_order_coefficient_checks']}.",
        f"Exact amplitude correction checks from shifted-binomial products and Stirling: {corrections['exact_amplitude_first_order_coefficient_checks']}.",
        "Parameters: c=2,4,8,16; m=1..20; profile coefficients j=0..12.",
        "Numerical remainders and 64-point circle samples are in first_correction_checks.csv.",
        "Circle samples are diagnostic; their maximum does not bound the unsampled circle.",
        "Generated LaTeX: diagnostic_tables.tex and optional first_correction_tables.tex.",
        "", "DIAGNOSTIC METHODS AND LIMITATIONS",
        "- Blocks q<=11 use retained coefficients from the exact finite-defect formula.",
        "- Blocks q>=12 use U_m*binom(2^m-m,n-m), with covering error <=m*2^(-(n-m)).",
        "- Radial sums include q<=24 and at most 220 coefficients of each block.",
        "- Within-block omitted terms are bounded by a decreasing geometric ratio.",
        "- For q>=25: block <= Rr/(1-2aR) * 2^((q+d)(q+d-1)/2) * r^(2^(q-1)).",
        "  Here m<=K/2 and k0=K+1-m<=K<=cK/2; therefore",
        "  binom(cK-m,k0)<=binom(cK,k0)<=binom(cK,K)<=R^(-K).",
        "  The last inequality follows by bounding the Kth term of (1+1/a)^(cK).",
        "  The ratios of successive majorants decrease; their geometric sum bounds all later blocks.",
        "- Ratios' analytic error majorants include all omitted terms and covering discrepancies.",
        "- Those majorants do not bound mpmath roundoff. No floating evaluation is interval-certified.",
        "- Numerical phase convergence is illustrative; it does not establish a natural boundary.",
        "- CSV and JSON files retain more digits than the compact tables above.",
        f"", f"Elapsed wall time: {elapsed:.2f} seconds.",
    ]
    (DATA / "verification.txt").write_text("\n".join(lines) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=64)
    parser.add_argument("--brute-n", type=int, default=6)
    parser.add_argument("--skip-figures", action="store_true")
    args = parser.parse_args()
    if args.max_n < 30:
        parser.error("--max-n must be at least 30 for the numerical diagnostics")
    if not 0 <= args.brute_n <= min(args.max_n, 7):
        parser.error("--brute-n must be between 0 and min(max-n,7)")
    DATA.mkdir(exist_ok=True)
    FIGURES.mkdir(exist_ok=True)
    mp.mp.dps = 100
    started = time.perf_counter()
    totals, exact = exact_checks(args.max_n, args.brute_n)
    print(f"Exact checks PASS: n <= {args.max_n}; {exact['independently_matching_triangle_cells']} triangle cells.", flush=True)
    blocks = block_diagnostics(totals)
    print("Exact block prefixes and numerical profiles complete.", flush=True)
    corrections = first_correction_checks(totals)
    print("Independent first-order coefficient checks and numerical residuals complete.", flush=True)
    radial = radial_diagnostics(totals)
    print("Numerical radial ratios and analytic error majorants complete.", flush=True)
    write_latex_tables(blocks, radial, corrections)
    if not args.skip_figures:
        scientific_figures(totals, radial)
    elapsed = time.perf_counter() - started
    write_summary(exact, blocks, radial, corrections, elapsed)
    print(f"Wrote data and figures to {ROOT}; elapsed {elapsed:.2f} s.", flush=True)


if __name__ == "__main__":
    main()
