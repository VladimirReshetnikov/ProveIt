#!/usr/bin/env python3
"""Reproduce rational Stieltjes certificates and the derivative-profile figure.

The rational endpoints are exact certificates by Theorem 6.1 and its
corollary (use equation labels in article.tex if numbering changes).
All mpmath evaluations and plots are separately labelled numerical checks.
No independence claim or interval-arithmetic claim is made for mpmath.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import platform

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]


def rational_json(x: Fraction) -> dict[str, str]:
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def stirling_coefficients(k: int, nmax: int) -> list[int]:
    """Coefficients of product_{j=1}^k (j+z), using exact integers."""
    p = [1] + [0] * nmax
    for j in range(1, k + 1):
        for n in range(min(j, nmax), 0, -1):
            p[n] = j * p[n] + p[n - 1]
        p[0] *= j
    return p


def elementary_recurrence(k: int, nmax: int) -> list[Fraction]:
    """Independent exact recurrence for product (1+z/j)."""
    p = [Fraction(1)] + [Fraction(0)] * nmax
    for j in range(1, k + 1):
        for n in range(min(j, nmax), 0, -1):
            p[n] += p[n - 1] / j
    return p


def certificate_table(quick: bool) -> dict:
    ks = [8, 16, 32, 64] if quick else [8, 16, 32, 64, 128, 256]
    rows = []
    exact_comparisons = 0
    signs = 0
    for k in ks:
        nmax = min(k, math.floor(3 * math.log(k)))
        p = stirling_coefficients(k, nmax)
        p_independent = elementary_recurrence(k, nmax)
        centers = [Fraction(v, math.factorial(k)) for v in p]
        assert centers == p_independent
        exact_comparisons += len(centers)
        assert centers[0] == 1
        # All terms are rational; no logarithm is used in any certificate.
        # The logarithm above only chooses which examples to print.
        prefactors = {
            h: Fraction(math.comb(k + h, h))
            * (Fraction(1, 2 ** (k + 1 - h))
               + Fraction(1, (k - h) * 2 ** (k - h)))
            for h in range(1, k)
        }
        for n in list(range(nmax + 1)) + [k + 1]:
            center = centers[n] if n <= nmax else Fraction(0)
            h, radius = min(
                ((h, b / h**n) for h, b in prefactors.items()),
                key=lambda pair: pair[1],
            )
            simple_radius = Fraction(k + 1) * (
                Fraction(1, 2**k) + Fraction(1, (k - 1) * 2 ** (k - 1))
            )
            assert prefactors[1] == simple_radius
            assert 0 < radius <= simple_radius
            lo, hi = center - radius, center + radius
            assert lo <= center <= hi
            positive = lo > 0
            signs += positive
            rows.append({
                "k": k, "n": n, "optimized_integer_radius_h": h,
                "normalization": "(-1)^(n+k)*gamma_n^(k)(1)/(k!*n!)",
                "center": rational_json(center),
                "radius": rational_json(radius),
                "lower": rational_json(lo), "upper": rational_json(hi),
                "strict_positive_sign_certified": positive,
            })
    return {
        "status": "exact rational construction passed",
        "meaning": (
            "Every inclusion follows from the proved analytic tail bound. "
            "The recurrence and endpoint arithmetic use Python integers and Fraction."
        ),
        "independent_exact_coefficient_comparisons": exact_comparisons,
        "certificate_count": len(rows),
        "positive_sign_certificates": signs,
        "rows": rows,
    }


def spectral_checks(quick: bool) -> dict:
    cases = []
    max_ratio = mp.mpf(0)
    ks = [3, 7] if quick else [3, 5, 8]
    aa = [mp.mpf("0.5"), mp.mpf(1)] if quick else [
        mp.mpf("0.5"), mp.mpf(1), mp.mpf("1.7")
    ]
    for k in ks:
        pp = [mp.mpf(1)] + [mp.mpf(0)] * 3
        for j in range(1, k + 1):
            for n in range(min(j, 3), 0, -1):
                pp[n] += pp[n - 1] / j
        for a in aa:
            for n in range(4):
                def poly(x):
                    return mp.factorial(n) * sum(
                        pp[j] * x**(n-j) / mp.factorial(n-j)
                        for j in range(min(n, k) + 1)
                    )
                M, radius = 24, mp.mpf(1)
                finite_sum = sum(
                    poly(-mp.log(a + m)) / (a + m)**(k + 1)
                    for m in range(M)
                )
                # Different analytic route: differentiate Hurwitz zeta in s.
                master = mp.diff(
                    lambda z: mp.rf(1 + z, k) / mp.factorial(k)
                    * mp.zeta(k + 1 + z, a), mp.mpf(0), n
                )
                b = a + M
                bound = mp.factorial(n) / radius**n * mp.fprod(
                    1 + radius/j for j in range(1, k + 1)
                ) * (b**(-k-1+radius) + b**(-k+radius)/(k-radius))
                observed = abs(master - finite_sum)
                ratio = observed / bound
                assert ratio <= 1 + mp.mpf("1e-45")
                max_ratio = max(max_ratio, ratio)
                cases.append({
                    "a": str(a), "k": k, "n": n, "terms": M,
                    "observed_difference": mp.nstr(observed, 30),
                    "proved_analytic_tail_majorant": mp.nstr(bound, 30),
                    "difference_to_bound_ratio": mp.nstr(ratio, 20),
                })
    return {
        "status": "passed",
        "arithmetic": "high-precision mpmath; not interval arithmetic",
        "count": len(cases),
        "maximum_difference_to_bound_ratio": mp.nstr(max_ratio, 25),
        "cases": cases,
    }


def profile_data(quick: bool) -> dict:
    ks = [64, 512] if quick else [64, 512, 4096]
    rows = []
    for k in ks:
        L = mp.log(k)
        nmax = int(mp.floor(3 * L))
        e = [mp.mpf(1)] + [mp.mpf(0)] * nmax
        for j in range(1, k + 1):
            jj = mp.mpf(j)
            for n in range(min(j, nmax), 0, -1):
                e[n] += e[n-1] / jj
        B = (k+1) * (mp.power(2, -k) + mp.power(2, 1-k)/(k-1))
        for n in range(nmax + 1):
            r = n / L
            norm = mp.factorial(n) / L**n
            first = norm * e[n]
            g = 1 / mp.gamma(1 + r)
            second = g * (1 + n/(2*L**2) * (
                mp.polygamma(1, 1+r) - mp.digamma(1+r)**2
            ))
            tail = norm * B
            rows.append({
                "k": k, "n": n, "r": mp.nstr(r, 40),
                "normalized_first_spectral_term": mp.nstr(first, 40),
                "reciprocal_gamma_profile": mp.nstr(g, 40),
                "profile_with_second_term": mp.nstr(second, 40),
                "first_profile_absolute_error": mp.nstr(abs(first-g), 30),
                "second_profile_absolute_error": mp.nstr(abs(first-second), 30),
                "spectral_tail_bound": mp.nstr(tail, 30),
                "log10_spectral_tail_bound": mp.nstr(mp.log10(tail), 25),
            })
    return {
        "arithmetic": "mpmath floating point; no interval arithmetic",
        "normalization": "(-1)^(n+k)*gamma_n^(k)(1)/(k!*log(k)^n)",
        "plotted_values": (
            "Numerical evaluation of the first spectral term. The exact "
            "mathematical first term differs from the normalized exact "
            "derivative by at most the stated analytic spectral-tail bound. "
            "That bound excludes floating-point roundoff and 40-digit "
            "decimal serialization error."
        ),
        "rows": rows,
    }


def draw_profile(data: dict) -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np
    from matplotlib.lines import Line2D

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 9,
        "axes.titlesize": 11, "axes.labelsize": 10,
        "axes.spines.top": False, "axes.spines.right": False,
        "pdf.fonttype": 42,
    })
    colors = ["#1f5c87", "#ca7028", "#397763"]
    fig, axes = plt.subplots(2, 1, figsize=(6.7, 6.1), sharex=True,
                             gridspec_kw={"height_ratios": [1.15, 1]})
    xs = np.linspace(0, 3, 301)
    axes[0].plot(xs, [float(1/mp.gamma(1+x)) for x in xs],
                 color="#252525", lw=1.6, label=r"$1/\Gamma(1+r)$")
    ks = sorted({row["k"] for row in data["rows"]})
    for color, k in zip(colors, ks):
        rr = [row for row in data["rows"] if row["k"] == k]
        xx = [float(row["r"]) for row in rr]
        yy = [float(row["normalized_first_spectral_term"]) for row in rr]
        axes[0].plot(xx, yy, "o", ms=3.1, color=color, alpha=0.85,
                     label=f"k = {k:,}")
        nonzero = [row for row in rr if row["n"] > 0]
        xx = [float(row["r"]) for row in nonzero]
        axes[1].semilogy(xx, [float(row["first_profile_absolute_error"])
                             for row in nonzero],
                        color=color, lw=1.2, marker="o", ms=2.5)
        axes[1].semilogy(xx, [float(row["second_profile_absolute_error"])
                             for row in nonzero],
                        color=color, lw=1.2, linestyle="--")
    axes[0].set_title("High parameter derivatives approach a reciprocal-gamma profile",
                      loc="left", pad=10)
    axes[0].set_ylabel("Normalized first spectral term")
    axes[0].legend(frameon=False, ncol=2, fontsize=8)
    axes[0].set_ylim(0, 1.22)
    axes[1].set_title("Effect of the explicit second term", loc="left", pad=8)
    axes[1].set_ylabel("Absolute profile error")
    axes[1].set_xlabel(r"$r=n/\log k$  (parameter $a=1$)")
    axes[1].legend(handles=[
        Line2D([0], [0], color="#555555", lw=1.4, label="Leading profile"),
        Line2D([0], [0], color="#555555", lw=1.4, linestyle="--",
               label="With second term")], frameon=False, fontsize=8)
    for ax in axes:
        ax.grid(True, alpha=0.17, lw=0.5)
        ax.set_xlim(0, 3.02)
    fig.tight_layout(pad=1.2)
    (ROOT / "figures").mkdir(exist_ok=True)
    fig.savefig(ROOT / "figures/derivative-profile.pdf", bbox_inches="tight")
    fig.savefig(ROOT / "figures/derivative-profile.png", dpi=180,
                bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--no-figure", action="store_true")
    args = parser.parse_args()
    mp.mp.dps = 55 if args.quick else 75
    certificates = certificate_table(args.quick)
    spectral = spectral_checks(args.quick)
    profile = profile_data(args.quick)
    if not args.no_figure:
        draw_profile(profile)
    result = {
        "status": "passed",
        "python": platform.python_version(), "mpmath": mp.__version__,
        "decimal_precision": mp.mp.dps, "quick_mode": args.quick,
        "rational_certificates": certificates,
        "spectral_tail_checks": spectral, "profile": profile,
    }
    (ROOT / "data").mkdir(exist_ok=True)
    output = ROOT / "data/parameter_asymptotics.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "passed",
        "rational_certificates": certificates["certificate_count"],
        "exact_recurrence_comparisons": certificates[
            "independent_exact_coefficient_comparisons"],
        "positive_sign_certificates": certificates["positive_sign_certificates"],
        "spectral_tail_checks": spectral["count"],
        "max_observed_tail_to_bound": spectral[
            "maximum_difference_to_bound_ratio"],
        "output": str(output),
    }, indent=2))


if __name__ == "__main__":
    main()
