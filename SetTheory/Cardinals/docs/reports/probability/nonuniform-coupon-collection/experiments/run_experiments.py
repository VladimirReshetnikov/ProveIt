#!/usr/bin/env python3
"""Reproduce the paper's coverage-certificate experiments and figures.

References are independent grouped inclusion-exclusion sums evaluated with Arb.
All terms of the grouped sums are included. The certified implementation under
test is imported from src/coupon_certificate.py and is not used to construct
the reference probability. Floating-point values are provided only for plots;
the JSON also retains the corresponding real-ball strings.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.metadata
import json
import math
import platform
import sys
from datetime import datetime, timezone
from fractions import Fraction
from itertools import product
from math import comb, factorial
from pathlib import Path
from time import perf_counter

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from flint import arb, ctx, fmpq

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from coupon_certificate import coverage_certificate  # noqa: E402

RESULTS = ROOT / "results"
FIGURES = ROOT / "figures"


def as_ball(value: Fraction | int) -> arb:
    if isinstance(value, Fraction):
        return arb(fmpq(value.numerator, value.denominator))
    return arb(value)


def grouped_inclusion_exclusion(groups, m: int, bits: int = 320) -> arb:
    """Full independent sum over count vectors of equal-probability groups."""
    groups = [(int(count), Fraction(weight)) for count, weight in groups]
    total_weight = sum(count * weight for count, weight in groups)
    with ctx.workprec(bits):
        answer = arb(0)
        for counts in product(*(range(count + 1) for count, _ in groups)):
            selected_weight = sum(
                count * weight for count, (_, weight) in zip(counts, groups)
            )
            coefficient = math.prod(
                comb(size, count) for count, (size, _) in zip(counts, groups)
            )
            base = 1 - selected_weight / total_weight
            term = coefficient * as_ball(base) ** m
            answer += -term if sum(counts) % 2 else term
        return answer


def expand_groups(groups):
    return [Fraction(weight) for count, weight in groups for _ in range(count)]


def target_time(weights, missing_mean: float) -> int:
    """Choose a concrete integer time; floating arithmetic only chooses m."""
    values = np.asarray([float(w) for w in weights], dtype=float)
    probabilities = values / values.sum()
    lo, hi = 0, max(1, len(weights))
    while float(np.exp(-hi * probabilities).sum()) > missing_mean:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if float(np.exp(-mid * probabilities).sum()) > missing_mean:
            lo = mid
        else:
            hi = mid
    return hi


def touchard_fraction(k: int, value: Fraction) -> Fraction:
    row = [1]
    for degree in range(1, k + 1):
        row = [0] + [
            (row[j - 1] if j - 1 < len(row) else 0)
            + j * (row[j] if j < len(row) else 0)
            for j in range(1, degree + 1)
        ]
    return sum((coefficient * value**j for j, coefficient in enumerate(row)), Fraction(0))


def numeric_record(certificate, reference: arb, reference_bits: int):
    with ctx.workprec(max(reference_bits, certificate.bits)):
        signed_error = reference - certificate.approximation
        absolute_error = abs(signed_error)
        radius = certificate.analytic_radius
        s, m = certificate.order, certificate.m
        hlz = 2 * s * 4**s * m**s * certificate.moments[2 * s]
        result = certificate.as_dict(45)
        result.update({
            "reference": reference.str(60),
            "reference_bits": reference_bits,
            "reference_radius": reference.rad().str(20),
            "signed_error": signed_error.str(45),
            "absolute_error": absolute_error.str(45),
            "hlz_majorant": hlz.str(45),
            "error_over_radius": (absolute_error / radius).str(45),
            "prior_over_radius": (certificate.prior_majorant / radius).str(30),
            "hlz_over_radius": (hlz / radius).str(30),
            "reference_contained": bool(certificate.enclosure.contains(reference)),
            "approximation_mid": float(certificate.approximation.mid()),
            "reference_mid": float(reference.mid()),
            "signed_error_mid": float(signed_error.mid()),
            "absolute_error_mid": float(absolute_error.mid()),
            "absolute_error_lower": float(absolute_error.lower()),
            "absolute_error_upper": float(absolute_error.upper()),
            "radius_mid": float(radius.mid()),
            "prior_majorant_mid": float(certificate.prior_majorant.mid()),
            "hlz_majorant_mid": float(hlz.mid()),
            "error_over_radius_mid": float((absolute_error / radius).mid()),
            "hlz_over_radius_mid": float((hlz / radius).mid()),
            "lambda_mid": float(certificate.poisson_missing_mean.mid()),
        })
        if not result["reference_contained"]:
            raise ArithmeticError("A reference interval is outside the certified enclosure.")
        if absolute_error.contains(0):
            raise ArithmeticError("Insufficient precision to resolve approximation error.")
        return result


def checkpoint(data):
    RESULTS.mkdir(parents=True, exist_ok=True)
    (RESULTS / "experiments.json").write_text(json.dumps(data, indent=2) + "\n")
    for name in ("uniform", "rare_two_coupon", "heterogeneous", "runtime"):
        records = data.get(name, [])
        if not records:
            continue
        columns = sorted(set().union(*(record.keys() for record in records)))
        with (RESULTS / f"{name}.csv").open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=columns)
            writer.writeheader()
            writer.writerows(records)


def run_uniform(data, bits, ref_bits):
    data["uniform"] = []
    for n in (50, 100, 300, 1000, 3000, 10000):
        m = math.floor(n * (math.log(n) + math.log(2)))
        start = perf_counter()
        reference = grouped_inclusion_exclusion([(n, 1)], m, ref_bits)
        reference_seconds = perf_counter() - start
        for order in range(1, 5):
            start = perf_counter()
            certificate = coverage_certificate([1] * n, m, order, bits)
            elapsed = perf_counter() - start
            record = numeric_record(certificate, reference, ref_bits)
            with ctx.workprec(ref_bits):
                constant = (
                    (-1)**order * (-arb(1) / 2).exp()
                    * as_ball(touchard_fraction(2 * order, Fraction(-1, 2)))
                    / (2**order * factorial(order))
                )
                scale = (arb(n).log() / n) ** order
                scaled_error = (reference - certificate.approximation) / scale
            record.update({
                "model": "uniform",
                "c": "log(2)",
                "groups": json.dumps([[n, 1]]),
                "reference_terms": n + 1,
                "reference_seconds": reference_seconds,
                "certificate_seconds": elapsed,
                "scaled_signed_error": scaled_error.str(40),
                "scaled_signed_error_mid": float(scaled_error.mid()),
                "asymptotic_signed_constant": constant.str(40),
                "asymptotic_signed_constant_mid": float(constant.mid()),
            })
            data["uniform"].append(record)
        checkpoint(data)
        print(f"uniform n={n}, m={m}: 4 orders complete", flush=True)


def run_rare(data, bits, ref_bits):
    data["rare_two_coupon"] = []
    for m in (100, 1000, 10000, 100000, 1000000):
        groups = [(1, 1), (1, m - 1)]
        reference = grouped_inclusion_exclusion(groups, m, ref_bits)
        for order in range(1, 5):
            certificate = coverage_certificate([1, m - 1], m, order, bits)
            record = numeric_record(certificate, reference, ref_bits)
            record.update({
                "model": "rare_two_coupon",
                "groups": json.dumps(groups),
                "rare_probability": str(Fraction(1, m)),
                "reference_terms": 4,
                "asymptotic_error_over_radius": 1,
            })
            data["rare_two_coupon"].append(record)
        checkpoint(data)
        print(f"rare two-coupon m={m}: 4 orders complete", flush=True)


def run_heterogeneous(data, bits, ref_bits):
    data["heterogeneous"] = []
    models = {
        "two_equal_size_groups": [(50, 1), (50, 3)],
        "one_rare_coupon": [(1, 1), (99, 100)],
    }
    for model, groups in models.items():
        weights = expand_groups(groups)
        for target_lambda in (2.0, 0.5, 0.05):
            m = target_time(weights, target_lambda)
            reference = grouped_inclusion_exclusion(groups, m, ref_bits)
            for order in range(1, 5):
                certificate = coverage_certificate(weights, m, order, bits)
                record = numeric_record(certificate, reference, ref_bits)
                record.update({
                    "model": model,
                    "groups": json.dumps(groups),
                    "target_lambda": target_lambda,
                    "reference_terms": math.prod(count + 1 for count, _ in groups),
                })
                data["heterogeneous"].append(record)
            checkpoint(data)
            print(f"heterogeneous {model}, lambda≈{target_lambda}, m={m}: complete", flush=True)


def run_runtime(data):
    data["runtime"] = []
    coverage_certificate(range(1, 11), 1000, 2, 128, group_equal=False)
    for n in (100, 1000, 10000, 100000):
        weights = [1 + (i % 997) for i in range(n)]
        m = target_time(weights, 0.5)
        for order in (2, 3):
            start = perf_counter()
            certificate = coverage_certificate(weights, m, order, 128, group_equal=False)
            elapsed = perf_counter() - start
            data["runtime"].append({
                "n": n, "m": m, "order": order, "bits": 128,
                "seconds": elapsed,
                "group_equal": False,
                "replicates": 1,
                "weights_rule": "w[i] = 1 + (i mod 997), i = 0,...,n-1",
                "lambda": certificate.poisson_missing_mean.str(30),
                "lambda_mid": float(certificate.poisson_missing_mean.mid()),
                "analytic_radius": certificate.analytic_radius.str(30),
                "radius_mid": float(certificate.analytic_radius.mid()),
                "enclosure": certificate.enclosure.str(35),
                "seconds_per_coupon": elapsed / n,
            })
            checkpoint(data)
            print(f"runtime n={n}, order={order}: {elapsed:.3f} seconds", flush=True)


def make_figures(data):
    FIGURES.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 9,
        "axes.labelsize": 9, "axes.titlesize": 10,
        "legend.fontsize": 8, "xtick.labelsize": 8, "ytick.labelsize": 8,
        "axes.spines.top": False, "axes.spines.right": False,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "savefig.dpi": 220,
    })
    colors = ("#005C97", "#D16800", "#27805D", "#9051A1")
    captions = {}

    if data.get("uniform"):
        fig, axes = plt.subplots(1, 2, figsize=(7.2, 3.25), layout="constrained")
        for order, color in enumerate(colors, 1):
            records = [row for row in data["uniform"] if row["order"] == order]
            ns = [row["n"] for row in records]
            axes[0].loglog(ns, [row["absolute_error_mid"] for row in records],
                           "o-", ms=4, color=color, label=fr"$s={order}$")
            axes[1].loglog(ns, [row["radius_mid"] for row in records],
                           "s-", ms=4, color=color, label=fr"$s={order}$")
        axes[0].set_title("Actual approximation error")
        axes[1].set_title("Proved error radius")
        for axis in axes:
            axis.set_xlabel("Number of coupon types, n")
            axis.grid(True, which="major", alpha=0.2)
            axis.legend(frameon=False)
        axes[0].set_ylabel(r"$|H(m)-A_s(m)|$")
        axes[1].set_ylabel(r"$R_s(m)$")
        fig.suptitle(r"Uniform collection at $m=\lfloor n(\log n+\log 2)\rfloor$", fontsize=11)
        for extension in ("pdf", "png"):
            fig.savefig(FIGURES / f"uniform_errors.{extension}", bbox_inches="tight")
        plt.close(fig)
        captions["uniform_errors"] = (
            "Uniform coupon probabilities p_i=1/n at m=floor(n(log n+log 2)). "
            "Left: absolute error of the Poisson–Charlier approximant through degree 2s-1. "
            "Right: the finite radius R_s from the main theorem. All n+1 terms of an independent "
            "grouped inclusion-exclusion sum were evaluated with 320-bit Arb for the reference; "
            "certificates use 224 bits by default. Plotted values are interval midpoints; "
            "outward interval strings and containment checks are retained in results/experiments.json."
        )

    if data.get("rare_two_coupon"):
        fig, axis = plt.subplots(figsize=(6.3, 3.3), layout="constrained")
        minimum = 1.0
        for order, color in enumerate(colors, 1):
            records = [row for row in data["rare_two_coupon"] if row["order"] == order]
            ratios = [row["error_over_radius_mid"] for row in records]
            minimum = min(minimum, *ratios)
            axis.semilogx([row["m"] for row in records], ratios,
                          "o-", color=color, ms=4, label=fr"$s={order}$")
        axis.axhline(1, color="#333333", linestyle="--", linewidth=1,
                     label="Sharpness limit")
        axis.set_ylim(max(0, minimum - 0.04), 1.015)
        axis.set_xlabel("Number of draws, m")
        axis.set_ylabel(r"$|H(m)-A_s(m)|/R_s(m)$")
        axis.set_title(r"Sharpness: two coupons with probabilities $1/m$ and $1-1/m$")
        axis.grid(True, which="major", alpha=0.2)
        axis.legend(frameon=False, ncol=3, loc="lower right")
        for extension in ("pdf", "png"):
            fig.savefig(FIGURES / f"sharpness_ratio.{extension}", bbox_inches="tight")
        plt.close(fig)
        captions["sharpness_ratio"] = (
            "Two-coupon sharpness family p_1=1/m, p_2=1-1/m, for m=10^2,...,10^6 "
            "and orders s=1,...,4. The ratio of the true approximation error to R_s approaches "
            "one, as proved in the article. References are complete four-term inclusion-exclusion "
            "sums at 320-bit precision. The smallest plotted errors remain resolved by the "
            "224-bit certificate arithmetic. This is a numerical illustration of a proved limit."
        )

    if data.get("runtime"):
        fig, axis = plt.subplots(figsize=(6.3, 3.3), layout="constrained")
        for order, color in ((2, colors[0]), (3, colors[1])):
            records = [row for row in data["runtime"] if row["order"] == order]
            ns = [row["n"] for row in records]
            times = [row["seconds"] for row in records]
            axis.loglog(ns, times, "o-", color=color, ms=5, label=fr"$s={order}$")
        records = [row for row in data["runtime"] if row["order"] == 2]
        base = next(row for row in records if row["n"] == 1000)
        ns = [row["n"] for row in records]
        axis.loglog(ns, [base["seconds"] * n / 1000 for n in ns], "--",
                    color="#555555", linewidth=1, label="Linear reference")
        axis.set_xlabel("Number of coupon types, n")
        axis.set_ylabel("Wall-clock time (seconds)")
        axis.set_title("Ungrouped evaluation with 128-bit Arb")
        axis.grid(True, which="major", alpha=0.2)
        axis.legend(frameon=False)
        for extension in ("pdf", "png"):
            fig.savefig(FIGURES / f"runtime_scaling.{extension}", bbox_inches="tight")
        plt.close(fig)
        captions["runtime_scaling"] = (
            "Measured wall-clock evaluation times with equal-weight grouping disabled, "
            "128-bit Arb, and integer weights w_i=1+(i mod 997), i=0,...,n-1. The integer "
            "draw count is chosen so that the Poissonized missing mean is at most 0.5. "
            "Each point is one timed run after one warm-up; timings include exact input "
            "normalization and certificate construction, exclude selection of m, and do not "
            "constitute a statistical benchmark. The dashed line is proportional to n and "
            "is anchored at the s=2, n=1000 measurement. The arithmetic-operation theorem "
            "is independent of these measurements; no unit-cost bit-complexity claim is made."
        )
    (RESULTS / "figure_captions.json").write_text(json.dumps(captions, indent=2) + "\n")


def write_report(data):
    lines = [
        "# Reproducible numerical results", "",
        "Run `python experiments/run_experiments.py` from the package directory. "
        "The script writes complete JSON data, one CSV per experiment family, and "
        "three PDF/PNG figures. The reference calculation independently evaluates "
        "every term of the grouped inclusion-exclusion formula with Arb.", "",
        "The JSON real-ball strings retain error bounds. Fields ending in `_mid` "
        "are readable floating-point midpoints for plots and tables. Each reference "
        "interval is required to be wholly contained in the returned certificate. "
        "The reported approximation error concerns the exact analytic approximant, "
        "enclosed by the computed ball; rounding and reference uncertainty are "
        "included in the error ball.", "",
        "## Environment", "",
        f"- Python: {platform.python_version()}",
        f"- python-flint: {data['metadata']['python_flint']}",
        f"- Matplotlib: {data['metadata']['matplotlib']}",
        f"- NumPy: {data['metadata']['numpy']}",
        f"- Certificate precision: {data['metadata']['certificate_bits']} bits",
        f"- Reference precision: {data['metadata']['reference_bits']} bits",
        "- Timing precision: 128 bits; equal-weight grouping disabled",
        f"- Core source SHA-256: `{data['metadata']['core_sha256']}`", "",
    ]
    comparison_rows = [row for name in ("uniform", "rare_two_coupon", "heterogeneous") for row in data.get(name, [])]
    lines += [f"All **{len(comparison_rows)}** reference-containment checks passed.", ""]
    if data.get("uniform"):
        lines += [
            "## Uniform collection at n = 10,000", "",
            "Here m = floor(n(log n + log 2)) = 99,034. The prior scalar "
            "comparison is the Hwang–Li–Zacharovas Lemma 5.3 majorant "
            "2s·4^s·m^s·M_(2s). The existing order-one lemma has the better "
            "coefficient m, so the generic s=1 comparison should not be "
            "mistaken for the strongest earlier order-one bound.", "",
            "| Order s | Absolute error | Certified radius R_s | HLZ generic bound / R_s |",
            "|---:|---:|---:|---:|",
        ]
        for row in data["uniform"]:
            if row["n"] == 10000:
                lines.append(f"| {row['order']} | {row['absolute_error_mid']:.6e} | {row['radius_mid']:.6e} | {row['hlz_over_radius_mid']:.6f} |")
        lines += ["", "The observed errors decrease with order. The radii certify all "
                  "these values but need not closely track the actual errors: signed "
                  "cancellation in uniform inclusion-exclusion is deliberately "
                  "discarded in the general positive-moment certificate.", ""]
    if data.get("rare_two_coupon"):
        lines += [
            "## Two-coupon sharpness family at m = 1,000,000", "",
            "Here p_1 = 1/m and p_2 = 1 - 1/m. The article proves that the "
            "error/radius ratio tends to one for every fixed order.", "",
            "| Order s | Absolute error / R_s | R_s |",
            "|---:|---:|---:|",
        ]
        for row in data["rare_two_coupon"]:
            if row["m"] == 1000000:
                lines.append(f"| {row['order']} | {row['error_over_radius_mid']:.12f} | {row['radius_mid']:.6e} |")
        lines += [""]
    if data.get("heterogeneous"):
        lines += [
            "## Heterogeneous cases", "",
            "Two 100-coupon models were evaluated at target Poissonized missing "
            "means 2, 0.5, and 0.05, for all four orders: fifty coupons of weight "
            "1 and fifty of weight 3; and one coupon of weight 1 with ninety-nine "
            "coupons of weight 100. The full references contain 2,601 and 200 "
            "terms respectively. Exact normalized rational weights, actual "
            "integer draw counts, achieved missing means, and all error balls "
            "are in heterogeneous.csv and experiments.json.", "",
        ]
    if data.get("runtime"):
        lines += [
            "## Ungrouped running times", "",
            "Weights are w_i = 1 + (i mod 997), indexed from zero. Each point "
            "is one timed run after a warm-up, includes normalization and "
            "certificate construction, and excludes choosing m. These "
            "measurements illustrate scaling; they are not a statistical "
            "benchmark or a bit-complexity theorem.", "",
            "| n | Order s | Seconds |",
            "|---:|---:|---:|",
        ]
        for row in data["runtime"]:
            lines.append(f"| {row['n']} | {row['order']} | {row['seconds']:.6f} |")
        lines += [""]
    lines += [
        "## Figure provenance", "",
        "Full captions, parameter choices, reference methods, and timing "
        "qualifications are saved in figure_captions.json. All figures were "
        "generated by Matplotlib from the recorded data, without fitted or "
        "fabricated observations. The scalar-bound comparison derives from "
        "Hwang, Li and Zacharovas, arXiv:2605.29633, Lemma 5.3; the separate "
        "33-based comparison is the total-variation-majorant specialization "
        "of Zacharovas, arXiv:2511.14324v2, Theorem 1.2.", "",
    ]
    (RESULTS / "README.md").write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sections", nargs="+", default=["uniform", "rare", "heterogeneous", "runtime", "figures"],
                        choices=["uniform", "rare", "heterogeneous", "runtime", "figures"])
    parser.add_argument("--bits", type=int, default=224)
    parser.add_argument("--reference-bits", type=int, default=320)
    args = parser.parse_args()
    path = RESULTS / "experiments.json"
    data = json.loads(path.read_text()) if path.exists() else {}
    data["metadata"] = {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "python": sys.version,
        "platform": platform.platform(),
        "python_flint": importlib.metadata.version("python-flint"),
        "matplotlib": matplotlib.__version__,
        "numpy": np.__version__,
        "flint_threads": ctx.threads,
        "certificate_bits": args.bits,
        "reference_bits": args.reference_bits,
        "core_sha256": hashlib.sha256((ROOT / "src" / "coupon_certificate.py").read_bytes()).hexdigest(),
        "reference_method": "Full grouped inclusion-exclusion with Arb; no reference uses the certificate code.",
        "float_fields": "Readable interval midpoints for plotting, not independent certificates.",
    }
    for section, function in (("uniform", run_uniform), ("rare", run_rare), ("heterogeneous", run_heterogeneous)):
        if section in args.sections:
            function(data, args.bits, args.reference_bits)
    if "runtime" in args.sections:
        run_runtime(data)
    checkpoint(data)
    if "figures" in args.sections:
        make_figures(data)
    write_report(data)
    print(f"Results written to {RESULTS}", flush=True)


if __name__ == "__main__":
    main()
