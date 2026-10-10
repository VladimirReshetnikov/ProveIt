#!/usr/bin/env python3
"""Static figures for the ProveIt translation/Euler continuation.

Dependencies: matplotlib, numpy, mpmath. Run from any directory.

The default verifier search supports both the present research workspace
and a final bundle with figures/ beside code/. An explicit --verifier path
can be supplied. These are formula-derived numerical visualizations, not
proof certificates. No finite-epsilon Euler curve is simulated.
"""
from __future__ import annotations

import argparse
import csv
import importlib.util
import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np


NAVY = "#173f68"
TEAL = "#087f8c"
RUST = "#bd562c"
INK = "#263443"
GRID = "#dde4ea"


def find_verifier(explicit):
    if explicit:
        return Path(explicit).resolve()
    here = Path(__file__).resolve()
    candidates = [
        here.parent.parent / "code" / "verify_translation.py",
        here.parent.parent.parent / "output" / "stieltjes_translation_research"
        / "code" / "verify_translation.py",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    raise FileNotFoundError("Use --verifier /path/to/verify_translation.py")


def load_verifier(path):
    spec = importlib.util.spec_from_file_location("translation_verifier", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def csv_write(path, header, rows):
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(header)
        writer.writerows(rows)


def style_axes(ax):
    ax.set_facecolor("white")
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color("#a0acb7")
        ax.spines[side].set_linewidth(0.7)
    ax.grid(axis="y", color=GRID, linewidth=0.6, zorder=0)
    ax.tick_params(colors=INK, width=0.7, length=3.5, pad=4)
    ax.set_axisbelow(True)


def save_figure(fig, stem):
    fig.savefig(stem.with_suffix(".pdf"), bbox_inches="tight",
                metadata={"Creator": "ProveIt research plotting script",
                          "Subject": "Formula-derived visualization; not a proof certificate"})
    fig.savefig(stem.with_suffix(".png"), dpi=240, bbox_inches="tight")
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verifier", type=Path)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    verifier_path = find_verifier(args.verifier)
    source = load_verifier(verifier_path)

    mp.mp.dps = 80
    count = 80
    coeff = source.coefficients(count)
    gamma1 = mp.stieltjes(1)
    limit = 2 + mp.pi**2 / 3

    def variance(h):
        h = mp.mpf(h)
        if h == 0 or h == 1:
            return mp.mpf(0)
        return source.variance_series(min(h, 1-h), coeff)

    def renormalized(h):
        # Algebraically cancel the logarithmic singular terms BEFORE
        # evaluating: no subtraction of V(h)/h and large logarithms.
        return (limit + (2*gamma1-mp.pi**2/3)*h
                - mp.fsum(2*b*h**(2*j-1)/(j*(2*j-1)) for j, b in coeff))

    hs = [mp.mpf(j)/800 for j in range(801)]
    left_vs = [variance(h) for h in hs[:401]]
    vs = left_vs + list(reversed(left_vs[:-1]))
    maximum = variance(mp.mpf("0.5"))
    endpoint_hs = [mp.exp(mp.log(mp.mpf("1e-8"))
                   + (mp.log(mp.mpf("0.5"))-mp.log(mp.mpf("1e-8")))*j/320)
                   for j in range(321)]
    endpoint_r = [renormalized(h) for h in endpoint_hs]
    # Check the independently arranged endpoint expression at benign h.
    for h in [mp.mpf("0.1"), mp.mpf("0.5")]:
        ell = mp.log(1/h)
        assert abs(renormalized(h)-(variance(h)/h-ell**2-2*ell)) < mp.mpf("1e-70")
    assert all(vs[j] == vs[-1-j] for j in range(401))
    assert all(vs[j] < vs[j+1] for j in range(400))
    tail = source.variance_tail_bound(mp.mpf("0.5"), count)

    csv_write(out / "gamma_translation_energy.csv", ["h", "V_series80"],
              [(mp.nstr(h, 40), mp.nstr(v, 60)) for h, v in zip(hs, vs)])
    csv_write(out / "gamma_endpoint_renormalized.csv",
              ["h", "natural_log_h", "R_series80", "limiting_constant"],
              [(mp.nstr(h, 40), mp.nstr(mp.log(h), 40), mp.nstr(r, 60),
                mp.nstr(limit, 60)) for h, r in zip(endpoint_hs, endpoint_r)])

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 14,
        "mathtext.fontset": "stix", "axes.labelsize": 15,
        "axes.titlesize": 15, "axes.titleweight": "semibold",
        "axes.labelcolor": INK, "text.color": INK,
        "xtick.labelsize": 13, "ytick.labelsize": 13,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "savefig.facecolor": "white", "figure.facecolor": "white",
    })

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(11.1, 4.15))
    fig.subplots_adjust(left=0.063, right=0.985, bottom=0.19, top=0.87, wspace=0.30)
    for panel in (ax, bx):
        style_axes(panel)
    ax.plot([float(h) for h in hs], [float(v) for v in vs], color=NAVY,
            linewidth=2.25, zorder=3)
    ax.plot([0.5], [float(maximum)], "o", color=RUST, markersize=5.8, zorder=4)
    ax.axvline(0.5, ymin=0, ymax=float(maximum)/3.08, color=RUST,
               alpha=0.45, linestyle=(0, (3, 3)), linewidth=0.85)
    ax.annotate("Unique maximum\n" + r"$V(1/2)=2.680722487980507\ldots$",
                xy=(0.5, float(maximum)), xytext=(0.50, 1.13),
                textcoords="data", ha="center", va="center", fontsize=13,
                arrowprops={"arrowstyle": "-", "color": RUST,
                            "lw": 0.85, "shrinkA": 5, "shrinkB": 7},
                bbox={"boxstyle": "round,pad=0.35", "fc": "white", "ec": "none"})
    ax.set(xlim=(0, 1), ylim=(0, 3.08), xlabel=r"Translation $h$", ylabel=r"$V(h)$")
    ax.set_xticks([0, .25, .5, .75, 1], ["0", r"$1/4$", r"$1/2$", r"$3/4$", "1"])
    ax.set_yticks([0, 1, 2, 3])
    ax.set_title("A   Gamma translation energy", loc="left", pad=12)

    logs = [float(mp.log(h)) for h in endpoint_hs]
    bx.plot(logs, [float(r) for r in endpoint_r], color=TEAL,
            linewidth=2.25, zorder=3)
    bx.axhline(float(limit), color=RUST, linestyle=(0, (4, 3)), linewidth=1.05)
    bx.text(-9.3, float(limit)+.095, r"Limit $2+\pi^2/3$", color=RUST,
            fontsize=13, ha="center", va="bottom")
    bx.set(xlim=(logs[0], logs[-1]), ylim=(3.30, 5.65),
           xlabel=r"$\log h\qquad(\ell=\log(1/h))$",
           ylabel=r"$V(h)/h-\ell^2-2\ell$")
    bx.set_xticks([-18, -12, -6, math.log(.5)], ["−18", "−12", "−6", r"$\log(1/2)$"])
    bx.set_yticks([3.5, 4.0, 4.5, 5.0, 5.5])
    bx.set_title("B   Renormalized endpoint behavior", loc="left", pad=12)
    save_figure(fig, out / "gamma_translation.pdf")

    # This is exactly the proved limiting function, not a finite-epsilon
    # sample from the original Euler sum.
    xs = np.unique(np.r_[np.linspace(.5, 1, 121), np.linspace(1, 16, 601), 4.0])
    ys = xs**(-.5) - xs**(-1)
    csv_write(out / "euler_limiting_profile.csv", ["x", "f_limiting"],
              [(format(x, ".17g"), format(y, ".17g")) for x, y in zip(xs, ys)])
    fig, ax = plt.subplots(figsize=(8.25, 3.75))
    fig.subplots_adjust(left=.087, right=.975, bottom=.20, top=.83)
    style_axes(ax)
    ax.axhline(0, color="#7c8996", linewidth=.85)
    ax.plot(xs, ys, color=NAVY, linewidth=2.3, zorder=3)
    ax.fill_between(xs, 0, ys, where=xs >= 1, color=TEAL, alpha=.075)
    ax.scatter([1, 4], [0, .25], color=[TEAL, RUST], s=34, zorder=4)
    ax.plot([4, 4], [0, .25], color=RUST, alpha=.6,
            linewidth=.8, linestyle=(0, (3, 3)))
    ax.annotate(r"Zero at $x=1$", xy=(1, 0), xytext=(2.3, -.21),
                ha="left", va="center", fontsize=13, color=TEAL,
                arrowprops={"arrowstyle": "-", "color": TEAL, "lw": .85,
                            "shrinkA": 4, "shrinkB": 5})
    ax.annotate(r"Maximum: $f(4)=1/4$", xy=(4, .25), xytext=(6.3, .335),
                ha="left", va="center", fontsize=13, color=RUST,
                arrowprops={"arrowstyle": "-", "color": RUST, "lw": .85,
                            "shrinkA": 4, "shrinkB": 6})
    ax.set(xlim=(.5, 16), ylim=(-.64, .40), xlabel=r"Scaled variable $x$",
           ylabel=r"$f(x)=x^{-1/2}-x^{-1}$")
    ax.set_xticks([1, 4, 8, 12, 16])
    ax.set_yticks([-.5, -.25, 0, .25], [r"$-1/2$", r"$-1/4$", "0", r"$1/4$"])
    ax.set_title("Proved limiting Euler profile", loc="left", pad=12)
    save_figure(fig, out / "euler_limiting_profile.pdf")

    metadata = {
        "status": "Formula-derived numerical visualizations; not proof certificates.",
        "gamma_source": "code/verify_translation.py: coefficients, variance_series, variance_tail_bound",
        "mpmath_decimal_precision": 80,
        "gamma_series_last_index": 80,
        "gamma_series_summation_indices": "j=2,...,80",
        "gamma_method": "For 0<h<=1/2 use variance_series; mirror V(1-h)=V(h); set endpoint limits to zero.",
        "endpoint_method": "R(h)=2+pi^2/3+(2*gamma_1-pi^2/3)*h-sum(2*b_j*h^(2*j-1)/(j*(2*j-1))).",
        "gamma_maximum_location": "1/2",
        "gamma_maximum_series_value": mp.nstr(maximum, 70),
        "gamma_series_uniform_tail_bound_h_at_most_one_half": mp.nstr(tail, 20),
        "endpoint_limit": mp.nstr(limit, 70),
        "endpoint_h_range": ["1e-8", "1/2"],
        "euler_function": "f(x)=x^(-1/2)-x^(-1), the proved limiting profile",
        "euler_domain": [0.5, 16],
        "euler_zero": 1,
        "euler_unique_maximum_location": 4,
        "euler_maximum_value": "1/4",
        "finite_epsilon_simulation": False,
        "files": ["gamma_translation.pdf", "gamma_translation.png",
                  "euler_limiting_profile.pdf", "euler_limiting_profile.png",
                  "gamma_translation_energy.csv", "gamma_endpoint_renormalized.csv",
                  "euler_limiting_profile.csv", "plot_research_figures.py"],
    }
    (out / "figure_data.json").write_text(json.dumps(metadata, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"output_directory": str(out),
                      "gamma_maximum": metadata["gamma_maximum_series_value"],
                      "uniform_series_tail_bound": metadata["gamma_series_uniform_tail_bound_h_at_most_one_half"],
                      "result": "figures and data generated"}, indent=2))


if __name__ == "__main__":
    main()
