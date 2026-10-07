#!/usr/bin/env python3
"""Reproduce the exact checks, numerical diagnostics and vector figures.

The backward recursion and all forward survival decisions use Python integers.
Finite-breakpoint certificates use fractions.Fraction, with exact rational
endpoints written to data/certificates.json. Decimal evaluations and gamma
products are numerical diagnostics, not interval-certified evaluations.

Run from any directory:
    python3 code/verify.py
Use --no-figures when NumPy or Matplotlib is unavailable. The exact
checks, thresholds and rational certificates use only Python's standard library.
The default largest K is 100000; no quadratic-sized arrays are created.

Index convention: a periodic tuple is (alpha_0,...,alpha_(p-1)), and the
transition from k-1 to k uses alpha_(k mod p), for k >= 2. The initial weight
is w_1=1. Threshold T_w(K) is the least initial integer surviving through K.
"""

from __future__ import annotations

import argparse
import csv
import heapq
import json
import math
import sys
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

PRECISION = 70


def dec(value: Fraction | int) -> Decimal:
    if isinstance(value, Fraction):
        return Decimal(value.numerator) / Decimal(value.denominator)
    return Decimal(value)


def ceil_div(numerator: int, denominator: int) -> int:
    return (numerator + denominator - 1) // denominator


def ceil_fraction(value: Fraction) -> int:
    return ceil_div(value.numerator, value.denominator)


def rational_record(value: Fraction) -> dict[str, str]:
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def decimal_pi() -> Decimal:
    """Machin's identity, evaluated using Decimal; this is not interval code."""
    def arctan_inverse(n: int) -> Decimal:
        x = Decimal(1) / n
        term = x
        total = term
        j = 1
        while True:
            term *= -(x * x)
            addend = term / (2 * j + 1)
            previous = total
            total += addend
            if total == previous:
                return total
            j += 1
    return 16 * arctan_inverse(5) - 4 * arctan_inverse(239)


@dataclass(frozen=True)
class Drift:
    name: str
    label: str
    alphas: tuple[Fraction, ...]
    active_zeros: bool = False
    closed_form: str | None = None
    weak_zero_frequency: Fraction | None = None

    @property
    def mean(self) -> Fraction:
        return sum(self.alphas, Fraction(0)) / len(self.alphas)

    @property
    def rho(self) -> Fraction:
        return Fraction(sum(a > 0 for a in self.alphas), len(self.alphas)) + self.eta

    @property
    def eta(self) -> Fraction:
        if self.weak_zero_frequency is not None:
            return self.weak_zero_frequency
        return Fraction(sum(a == 0 and self.active_zeros for a in self.alphas), len(self.alphas))

    def value(self, z: Fraction, right: bool = False) -> Fraction:
        """D(z), or its right limit. Integrals are unaffected at breakpoints."""
        total = 0
        for alpha in self.alphas:
            if alpha > 0:
                v = alpha * z
                total += v.numerator // v.denominator + 1 if right else max(1, ceil_fraction(v))
        return Fraction(total, len(self.alphas)) + self.eta

    def intervals(self, endpoint: Fraction):
        """Exact endpoints and exact constant drifts, using O(p) heap storage."""
        if endpoint <= 0:
            return
        heap = []
        for index, alpha in enumerate(self.alphas):
            if alpha > 0:
                heapq.heappush(heap, (1 / alpha, index, 1))
        left = Fraction(0)
        d = self.rho
        while left < endpoint:
            right = min(heap[0][0] if heap else endpoint, endpoint)
            yield left, right, d
            if right == endpoint:
                break
            count = 0
            while heap and heap[0][0] == right:
                _, index, n = heapq.heappop(heap)
                count += 1
                heapq.heappush(heap, (Fraction(n + 1) / self.alphas[index], index, n + 1))
            d += Fraction(count, len(self.alphas))
            left = right

    def exact_t(self, endpoint: Fraction) -> Fraction:
        result = Fraction(1)
        for left, right, d in self.intervals(endpoint):
            result *= (left + d) / (right + d)
        return result

    def gamma_data(self) -> tuple[int, list[tuple[Fraction, Fraction]]]:
        """L=H*(product Gamma(B_i)/Gamma(A_i))^(mean+1)."""
        period = math.lcm(*(a.denominator for a in self.alphas))
        scale = (self.mean + 1) * period
        arguments = [((left + d) / scale, (right + d) / scale)
                     for left, right, d in self.intervals(Fraction(period))]
        return period, arguments

    def numerical_constant(self, pi: Decimal) -> Decimal:
        if self.closed_form == "1/pi":
            return 1 / pi
        if self.closed_form == "1/(2*pi)":
            return 1 / (2 * pi)
        if self.closed_form == "pi/8":
            return pi / 8
        period, arguments = self.gamma_data()
        log_value = math.log(period) + float(self.mean + 1) * math.fsum(
            math.lgamma(float(b)) - math.lgamma(float(a)) for a, b in arguments)
        return Decimal(str(math.exp(log_value)))


ONE = Drift("one", r"$\alpha=(1)$", (Fraction(1),), closed_form="1/pi")
MIXED = Drift("mixed", r"$\alpha=(1/2,3/2)$", (Fraction(1, 2), Fraction(3, 2)))
PLATEAU = Drift("plateau", r"$(0,2)$, plateau", (Fraction(0), Fraction(2)), False, "1/(2*pi)")
ACTIVE = Drift("active", r"$(0,2)$, active zero phase", (Fraction(0), Fraction(2)), True, "pi/8")
TRIPLE = Drift("triple", r"$\alpha=(1/2,1,3/2)$", (Fraction(1, 2), Fraction(1), Fraction(3, 2)))
TRIPLE_PERMUTED = Drift("triple_permuted", r"$\alpha=(1/2,3/2,1)$", (Fraction(1, 2), Fraction(3, 2), Fraction(1)))
DRIFTS = (ONE, MIXED, PLATEAU, ACTIVE, TRIPLE, TRIPLE_PERMUTED)
DENSITY_DRIFTS = tuple(
    Drift("density_" + str(theta).replace("/", "_"), str(theta),
          (Fraction(0), Fraction(2)), weak_zero_frequency=theta / 2)
    for theta in (Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(3, 4), Fraction(1)))


@dataclass(frozen=True)
class Model:
    name: str
    label: str
    drift: Drift
    epsilon: Fraction | None = None

    def ratio(self, k: int) -> tuple[int, int]:
        if self.epsilon is not None:
            j = k // 2
            a, b = self.epsilon.numerator, self.epsilon.denominator
            if k % 2 == 0:
                return b * j * j + a, b * j * j
            return b * j * (j + 1), b * j * j + a
        alpha = self.drift.alphas[k % len(self.drift.alphas)]
        if alpha > 0:
            a, b = alpha.numerator, alpha.denominator
            return b * k + a, b * k
        if self.drift.active_zeros:
            return k * k + 1, k * k
        return 1, 1

    def threshold(self, K: int, target: int = 1) -> int:
        value = target
        for k in range(K, 1, -1):
            numerator, denominator = self.ratio(k)
            value = ceil_div(numerator * value, denominator)
        return value

    def forward(self, initial: int, K: int) -> int:
        value = initial
        for k in range(2, K + 1):
            numerator, denominator = self.ratio(k)
            value = value * denominator // numerator
        return value

    def weights(self, selected: list[int]) -> dict[int, Decimal]:
        if self.epsilon is not None:
            result = {}
            for k in selected:
                j = (k + 1) // 2
                weight = Fraction(j) if k % 2 else Fraction(j) + self.epsilon / j
                result[k] = dec(weight)
            return result
        wanted = set(selected)
        result = {}
        value = Decimal(1)
        if 1 in wanted:
            result[1] = value
        for k in range(2, max(selected) + 1):
            numerator, denominator = self.ratio(k)
            value *= Decimal(numerator) / Decimal(denominator)
            if k in wanted:
                result[k] = value
        return result


MODELS = tuple(Model(drift.name, drift.label, drift) for drift in DRIFTS) + (
    Model("epsilon_0", r"$\varepsilon=0$", PLATEAU, Fraction(0)),
    Model("epsilon_half", r"$\varepsilon=1/2$", ACTIVE, Fraction(1, 2)),
    Model("epsilon_100", r"$\varepsilon=1/100$", ACTIVE, Fraction(1, 100)),
    Model("epsilon_10000", r"$\varepsilon=1/10000$", ACTIVE, Fraction(1, 10000)),
)


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def run_exact_checks() -> dict:
    inverse_cases = 0
    exhaustive_cases = 0
    for model in MODELS:
        for K in range(1, 41):
            for target in range(1, 5):
                threshold = model.threshold(K, target)
                assert model.forward(threshold, K) >= target, (model.name, K, target)
                assert model.forward(threshold - 1, K) < target, (model.name, K, target)
                inverse_cases += 2
            if K <= 15:
                threshold = model.threshold(K)
                for initial in range(threshold + 3):
                    assert (model.forward(initial, K) >= 1) == (initial >= threshold)
                    exhaustive_cases += 1
        for k in range(2, 101):
            numerator, denominator = model.ratio(k)
            assert numerator >= denominator > 0
    return {
        "status": "passed",
        "model_count": len(MODELS),
        "inverse_boundary_checks": inverse_cases,
        "exhaustive_small_survival_checks": exhaustive_cases,
        "description": "Exact integer ceil/floor division; each boundary tested from both sides. "
                       "This verifies the implementation on finitely many inputs, not the asymptotic theorem.",
    }


def collect_thresholds(max_K: int, pi: Decimal):
    geometric = {int(round(10 ** (1 + j * (math.log10(max_K) - 1) / 27))) for j in range(28)}
    requested = {100, 1000, 10000, 100000}
    selected = sorted({k for k in geometric | requested | {max_K} if 2 <= k <= max_K})
    rows = []
    for model in MODELS:
        weights = model.weights(selected)
        limit = model.drift.numerical_constant(pi)
        for K in selected:
            threshold = model.threshold(K)
            normalized = Decimal(threshold) / (K * weights[K])
            rows.append({
                "model": model.name,
                "K": K,
                "T": threshold,
                "w_K_decimal": str(weights[K]),
                "T_over_K_w_K_decimal": str(normalized),
                "limit_numerical": str(limit),
                "relative_error_numerical": str(normalized / limit - 1),
                "integer_threshold_exact": True,
                "floating_or_decimal_values_certified": False,
            })
    return rows


def collect_certificates(endpoint: int, pi: Decimal):
    exact = []
    summary = []
    for drift in DRIFTS + DENSITY_DRIFTS:
        for z_int in sorted({min(100, endpoint), endpoint}):
            z = Fraction(z_int)
            t = drift.exact_t(z)
            exponent = drift.mean + 1
            assert exponent.denominator == 1
            t_power = t ** exponent.numerator
            lower = (z + drift.eta / exponent) * t_power
            upper = (z + drift.rho / exponent) * t_power
            assert lower < upper
            limit = drift.numerical_constant(pi)
            assert dec(lower) < limit < dec(upper), (drift.name, z_int)
            exact.append({
                "drift": drift.name,
                "z": str(z),
                "mean": str(drift.mean),
                "rho": str(drift.rho),
                "eta": str(drift.eta),
                "t_exact": rational_record(t),
                "L_lower_exact": rational_record(lower),
                "L_upper_exact": rational_record(upper),
            })
            summary.append({
                "drift": drift.name,
                "z": z_int,
                "L_lower_rounded": str(dec(lower)),
                "L_upper_rounded": str(dec(upper)),
                "absolute_width_rounded": str(dec(upper - lower)),
                "relative_width_exact": str((upper - lower) / lower),
                "limit_numerical": str(limit),
                "rational_endpoints_certified_by_theorem": True,
                "decimal_evaluation_interval_certified": False,
            })
    return exact, summary


def gamma_records(pi: Decimal):
    result = []
    for drift in DRIFTS + DENSITY_DRIFTS:
        H, arguments = drift.gamma_data()
        result.append({
            "drift": drift.name,
            "H": H,
            "mean": str(drift.mean),
            "exponent": str(drift.mean + 1),
            "gamma_arguments": [{"A": str(a), "B": str(b)} for a, b in arguments],
            "formula": "L = H * (product_i Gamma(B_i) / Gamma(A_i))^(mean+1)",
            "closed_form": drift.closed_form,
            "limit_numerical": str(drift.numerical_constant(pi)),
            "decimal_or_float_evaluation_certified": False,
        })
    return result


def collect_profiles(K: int):
    rows = []
    selected = {max(1, int(K * j / 500)) for j in range(25, 501)}
    for model in MODELS:
        if model.name not in {"epsilon_0", "epsilon_half", "epsilon_10000"}:
            continue
        q = 1
        if K in selected:
            rows.append({"model": model.name, "K": K, "k": K, "t": 1.0,
                         "q_exact": q, "q_over_K": q / K, "q_over_k": q / K})
        for k in range(K, 1, -1):
            numerator, denominator = model.ratio(k)
            q = ceil_div(numerator * q, denominator)
            j = k - 1
            if j in selected:
                rows.append({"model": model.name, "K": K, "k": j, "t": j / K,
                             "q_exact": q, "q_over_K": q / K, "q_over_k": q / j})
    return rows


def continuum_samples(drift: Drift, endpoint: int = 100):
    """Floating samples only; rational certificates are produced separately."""
    rows = [{"drift": drift.name, "z": 0.0, "t": 1.0, "y": 0.0}]
    t_left = 1.0
    for left_q, right_q, d_q in drift.intervals(Fraction(endpoint)):
        left, right, d = float(left_q), float(right_q), float(d_q)
        for j in range(1, 13):
            z = left + (right - left) * j / 12
            t = t_left * (left + d) / (z + d)
            rows.append({"drift": drift.name, "z": z, "t": t, "y": t * z})
        t_left *= (left + d) / (right + d)
    return rows


def make_figures(output: Path, threshold_rows, profile_rows, pi: Decimal):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 9,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.grid": True, "grid.alpha": 0.18,
        "axes.labelsize": 9, "legend.fontsize": 7.3,
        "xtick.labelsize": 8, "ytick.labelsize": 8,
        "savefig.bbox": "tight", "pdf.fonttype": 42,
    })
    colors = {"one": "#276FBF", "mixed": "#7D5BA6", "triple": "#DF8C23",
              "triple_permuted": "#A96816", "epsilon_0": "#276FBF",
              "epsilon_half": "#B43C4D", "epsilon_100": "#CF7C35",
              "epsilon_10000": "#2A9075"}
    by_model = {model.name: [r for r in threshold_rows if r["model"] == model.name] for model in MODELS}
    fig, axes = plt.subplots(1, 2, figsize=(7.05, 3.15), layout="constrained")
    for name in ("one", "mixed", "triple", "triple_permuted"):
        model = next(m for m in MODELS if m.name == name)
        rows = by_model[name]
        axes[0].plot([r["K"] for r in rows], [float(r["T_over_K_w_K_decimal"]) for r in rows],
                     color=colors[name], lw=1.3, marker="o" if name != "triple_permuted" else "x",
                     markersize=2.3, label=model.label)
        if name != "triple_permuted":
            axes[0].axhline(float(model.drift.numerical_constant(pi)), color=colors[name], ls=":", lw=1)
    for name in ("epsilon_0", "epsilon_half", "epsilon_100", "epsilon_10000"):
        model = next(m for m in MODELS if m.name == name)
        rows = by_model[name]
        axes[1].plot([r["K"] for r in rows], [float(r["T_over_K_w_K_decimal"]) for r in rows],
                     color=colors[name], lw=1.3, marker="o", markersize=2.1, label=model.label)
    for value, color, label, offset in [(float(1 / (2 * pi)), colors["epsilon_0"], r"$1/(2\pi)$", .007),
                                       (float(pi / 8), colors["epsilon_half"], r"$\pi/8$", -.029)]:
        axes[1].axhline(value, color=color, ls=":", lw=1.1)
        axes[1].text(float(max(r["K"] for r in threshold_rows)) * .72, value + offset,
                     label, color=color, ha="right", fontsize=9)
    for ax in axes:
        ax.set_xscale("log")
        ax.set_xlabel(r"terminal stage $K$")
        ax.set_ylabel(r"$T_w(K)/(K w_K)$")
        ax.legend(loc="upper right", framealpha=.93)
    axes[0].set_title("Periodic positive phases")
    axes[1].set_title("Uniformly small weight perturbations")
    fig.savefig(output / "normalized_thresholds.pdf")
    fig.savefig(output / "normalized_thresholds.png", dpi=180)
    plt.close(fig)

    fig, axes = plt.subplots(1, 2, figsize=(7.05, 3.1), layout="constrained")
    for drift, color in ((PLATEAU, "#276FBF"), (ACTIVE, "#B43C4D")):
        zs = np.linspace(0.00001, 3.00001, 1201)
        ds = [(math.ceil(2 * z) + int(drift.active_zeros)) / 2 for z in zs]
        axes[0].plot(zs, ds, color=color, lw=1.4,
                     label=r"$\varepsilon>0$" if drift.active_zeros else r"$\varepsilon=0$")
    axes[0].plot([0, 3], [0, 3], color="#555555", ls=":", lw=1, label=r"mean drift $z$")
    axes[0].set(xlim=(0, 3), ylim=(0, 3.7), xlabel=r"$z=q/k$", ylabel=r"effective drift $D(z)$",
                title="A positive increment survives rounding")
    axes[0].legend(loc="upper left")
    for drift, color in ((PLATEAU, "#276FBF"), (ACTIVE, "#B43C4D")):
        samples = continuum_samples(drift)
        relevant = [row for row in samples if row["t"] >= .1]
        axes[1].plot([r["t"] for r in relevant], [r["y"] for r in relevant],
                     color=color, lw=1.5, label=r"limiting profile, $\varepsilon>0$" if drift.active_zeros
                     else r"limiting profile, $\varepsilon=0$")
    for name, marker, color in (("epsilon_0", "o", "#276FBF"),
                                ("epsilon_10000", "x", "#2A9075")):
        relevant = sorted([row for row in profile_rows if row["model"] == name and row["t"] >= .1],
                          key=lambda r: r["t"])[::15]
        axes[1].plot([r["t"] for r in relevant], [r["q_over_K"] for r in relevant],
                     color=color, marker=marker, ms=3, linestyle="none",
                     label=r"exact, $\varepsilon=10^{-4}$" if name.endswith("10000") else r"exact, $\varepsilon=0$")
    axes[1].set(xlim=(.1, 1), xlabel=r"$t=k/K$", ylabel=r"$q_k/K$", title="Backward trajectories")
    axes[1].legend(loc="upper right", fontsize=7)
    fig.savefig(output / "drift_and_profiles.pdf")
    fig.savefig(output / "drift_and_profiles.png", dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(5.25, 2.7), layout="constrained")
    ax.plot([0, 1], [float(pi / 8), float(pi / 8)], color="#B43C4D", lw=1.7)
    ax.scatter([0], [float(pi / 8)], s=46, facecolor="white", edgecolor="#B43C4D", zorder=4)
    ax.scatter([0], [float(1 / (2 * pi))], s=42, color="#276FBF", zorder=4)
    ax.annotate(r"$L(\varepsilon)=\pi/8$ for every $0<\varepsilon<1$", (.45, float(pi / 8)),
                xytext=(.25, .424), fontsize=9)
    ax.annotate(r"$L(0)=1/(2\pi)$", (0, float(1 / (2 * pi))), xytext=(.10, .185), fontsize=9)
    ax.text(.31, .27, r"$\sup_k |w_k^{(\varepsilon)}-w_k^{(0)}|=\varepsilon$", fontsize=10)
    ax.set(xlim=(-.035, 1.01), ylim=(.12, .46), xlabel=r"uniform weight perturbation $\varepsilon$",
           ylabel=r"$L(\varepsilon)=\lim T_w(K)/(K w_K)$")
    fig.savefig(output / "constant_discontinuity.pdf")
    fig.savefig(output / "constant_discontinuity.png", dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(5.25, 2.9), layout="constrained")
    theta = np.linspace(0, 1, 301)
    limit = [.5 * math.exp(2 * (math.lgamma(1 + x / 2) - math.lgamma((1 + x) / 2))) for x in theta]
    ax.plot(theta, limit, color="#7D5BA6", lw=1.8)
    selected_x = [float(d.eta * 2) for d in DENSITY_DRIFTS]
    selected_y = [float(d.numerical_constant(pi)) for d in DENSITY_DRIFTS]
    ax.scatter(selected_x, selected_y, color="#7D5BA6", s=25, zorder=4,
               label="rational certificate locations")
    ax.set(xlim=(-.02, 1.02), ylim=(.14, .42), xlabel=r"active fraction $\theta$ among weak phases",
           ylabel=r"$L_\theta$", title="The constant varies with activity density")
    ax.text(.04, .36, r"$L_\theta=\frac{1}{2}\left[\frac{\Gamma(1+\theta/2)}{\Gamma((1+\theta)/2)}\right]^2$",
            fontsize=13)
    ax.legend(loc="lower right")
    fig.savefig(output / "weak_phase_density.pdf")
    fig.savefig(output / "weak_phase_density.png", dpi=180)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--max-K", type=int, default=100000)
    parser.add_argument("--certificate-z", type=int, default=1000)
    parser.add_argument("--no-figures", action="store_true")
    args = parser.parse_args()
    if args.max_K < 10 or args.certificate_z < 1:
        parser.error("--max-K must be at least 10 and --certificate-z must be positive")
    data = args.output / "data"
    figures = args.output / "figures"
    data.mkdir(parents=True, exist_ok=True)
    figures.mkdir(parents=True, exist_ok=True)
    with localcontext() as context:
        context.prec = PRECISION
        pi = decimal_pi()
        verification = run_exact_checks()
        print(json.dumps(verification, indent=2), flush=True)
        thresholds = collect_thresholds(args.max_K, pi)
        write_csv(data / "thresholds.csv", thresholds)
        print(f"Wrote {len(thresholds)} exact threshold diagnostics.", flush=True)
        certificates, certificate_summary = collect_certificates(args.certificate_z, pi)
        (data / "certificates.json").write_text(json.dumps(certificates, indent=2) + "\n", encoding="utf-8")
        write_csv(data / "certificate_bounds.csv", certificate_summary)
        (data / "gamma_products.json").write_text(json.dumps(gamma_records(pi), indent=2) + "\n", encoding="utf-8")
        verification["exact_rational_certificate_count"] = len(certificates)
        verification["decimal_precision"] = PRECISION
        verification["numerical_note"] = ("Integer thresholds and stored rational fractions are exact. "
            "Decimal and floating-point values are rounded diagnostics, not directed-rounding intervals.")
        (data / "verification.json").write_text(json.dumps(verification, indent=2) + "\n", encoding="utf-8")
        profiles = collect_profiles(min(args.max_K, 10000))
        write_csv(data / "profile_samples.csv", profiles)
        write_csv(data / "limiting_profiles.csv", continuum_samples(PLATEAU) + continuum_samples(ACTIVE))
        print(f"Wrote {len(certificates)} exact rational certificates.", flush=True)
        if not args.no_figures:
            make_figures(figures, thresholds, profiles, pi)
            print("Wrote four vector PDF figures and PNG previews.", flush=True)
        for row in thresholds:
            if row["K"] in {100, 1000, 10000, 100000}:
                print(f"{row['model']:18s} K={row['K']:6d} T={row['T']:12d} "
                      f"T/(K*w_K)={float(row['T_over_K_w_K_decimal']):.12f}")


if __name__ == "__main__":
    main()
