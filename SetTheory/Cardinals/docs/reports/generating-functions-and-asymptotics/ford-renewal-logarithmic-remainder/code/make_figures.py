#!/usr/bin/env python3
"""Render manuscript figures and tables from the recorded numerical data.

This program plots diagnostics; it neither proves nor certifies bounds.
Run from the package root. By default all new outputs go to rerun/.
"""
from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def rows(path: Path):
    with path.open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream))


def scientific(value: str) -> str:
    number = float(value)
    if number == 0:
        return "0"
    exponent = math.floor(math.log10(abs(number)))
    mantissa = number / 10**exponent
    return rf"{mantissa:.3f}\times10^{{{exponent}}}"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=Path("data"))
    parser.add_argument("--out", type=Path, default=Path("rerun"))
    args = parser.parse_args()
    figure_dir = args.out / "figures"
    table_dir = args.out / "data"
    figure_dir.mkdir(parents=True, exist_ok=True)
    table_dir.mkdir(parents=True, exist_ok=True)
    recurrence = rows(args.input / "recurrence.csv")
    endpoint = rows(args.input / "endpoint_spectral_integral.csv")
    products = rows(args.input / "product_convergence.csv")

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 10,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.labelcolor": "#18364A", "text.color": "#18364A",
        "axes.titleweight": "bold", "axes.grid": True,
        "grid.alpha": 0.2, "pdf.fonttype": 42, "ps.fonttype": 42,
        "savefig.facecolor": "white",
    })
    teal, blue, orange, purple = "#087F8C", "#255F9E", "#C26B22", "#865997"

    fig, ax = plt.subplots(1, 2, figsize=(10.2, 3.45), constrained_layout=True)
    early = [r for r in recurrence if int(r["n"]) >= 50]
    ax[0].plot([int(r["n"]) for r in early],
               [float(r["normalized_b_n"]) for r in early],
               color=teal, label="Recurrence")
    ep_early = [r for r in endpoint if float(r["n"]) >= 1000 and float(r["n"]) <= 1e6]
    ax[0].plot([float(r["n"]) for r in ep_early],
               [float(r["normalized_b_n"]) for r in ep_early],
               "o-", color=teal, markersize=4, label="Positive integral")
    ax[0].axhline(1, color=orange, linestyle="--", label="Limit = 1")
    ax[0].set(xscale="log", xlabel="$n$", ylabel=r"$n^2(\log n)^2 E_n$",
              title="A slow approach with an overshoot")
    ax[0].legend(frameon=False, fontsize=8, loc="lower right")
    late = [r for r in endpoint if float(r["n"]) >= 1e4]
    xs = [math.log10(float(r["n"])) for r in late]
    ax[1].plot(xs, [float(r["normalized_b_n"])-1 for r in late],
               "o-", color=teal, markersize=4, label="Positive integral")
    ax[1].plot(xs, [2/(x*math.log(10)) for x in xs], "--", color=orange,
               label=r"First correction: $2/\log n$")
    ax[1].set(xscale="log", yscale="log", xlabel=r"$\log_{10}n$",
              ylabel=r"$n^2(\log n)^2 E_n-1$",
              title="The logarithmic rate becomes visible")
    ax[1].legend(frameon=False, fontsize=8)
    fig.savefig(figure_dir / "normalized_remainder.pdf")
    fig.savefig(figure_dir / "normalized_remainder.png", dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(1, 2, figsize=(10.2, 3.5), constrained_layout=True)
    for order, color in [(0, blue), (1, orange), (3, teal), (4, purple)]:
        ax[0].plot([int(r["n"]) for r in early],
                   [abs(float(r[f"relative_error_K{order}"])) for r in early],
                   color=color, label=f"Through c{order}")
    ax[0].set(xscale="log", yscale="log", xlabel="$n$",
              ylabel="Absolute relative error", title="Fixed logarithmic truncations")
    ax[0].legend(frameon=False, fontsize=8)
    finite = [r for r in endpoint if float(r["n"]) <= 1000]
    for key, label, color in [
        ("relative_error_sector0", "One algebraic term", blue),
        ("relative_error_sectors01", "Two algebraic terms", orange),
        ("relative_error_sectors012", "Three algebraic terms", teal),
    ]:
        ax[1].plot([float(r["n"]) for r in finite],
                   [abs(float(r[key])) for r in finite],
                   "o-", color=color, markersize=4, label=label)
    ax[1].set(xscale="log", yscale="log", xlabel="$n$",
              ylabel="Absolute relative error", title="Keeping the logarithmic integrals")
    ax[1].legend(frameon=False, fontsize=8)
    fig.savefig(figure_dir / "approximation_errors.pdf")
    fig.savefig(figure_dir / "approximation_errors.png", dpi=180)
    plt.close(fig)

    selected = {"100", "1000", "10000", "1000000", "10000000000",
                "100000000000000000000", "1"+"0"*50, "1"+"0"*100}
    lines = []
    for r in endpoint:
        if r["n"] not in selected:
            continue
        n = int(r["n"])
        power = len(str(n))-1
        label = rf"10^{{{power}}}" if n == 10**power else str(n)
        lines.append(rf"${label}$ & {float(r['normalized_b_n']):.10f} \\")
    (table_dir / "table_normalized.tex").write_text("\n".join(lines)+"\n", encoding="utf-8")
    lines = []
    for r in endpoint:
        if r["n"] in {"256", "500", "1000"}:
            lines.append(rf"{r['n']} & ${scientific(r['relative_error_sector0'])}$ & "
                         rf"${scientific(r['relative_error_sectors01'])}$ & "
                         rf"${scientific(r['relative_error_sectors012'])}$ \\")
    (table_dir / "table_sector_errors.tex").write_text("\n".join(lines)+"\n", encoding="utf-8")
    lines = []
    for r in products:
        if int(r["N"]) in {1, 2, 5, 10, 20, 50, 1000}:
            lines.append(rf"{r['N']} & {r['C_N'][:24]} \\")
    (table_dir / "table_product.tex").write_text("\n".join(lines)+"\n", encoding="utf-8")
    print(f"Wrote two figures (PDF/PNG) and three table fragments under {args.out}")


if __name__ == "__main__":
    main()
