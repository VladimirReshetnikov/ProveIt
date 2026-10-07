#!/usr/bin/env python3
"""Create the two vector PDF figures for the partition article.

Dependencies used for the checked build:
    Python 3.12.14
    NumPy 2.3.5
    mpmath 1.3.0
    Matplotlib 3.10.8

No TeX installation is needed: labels use Matplotlib's mathtext, and PDF fonts
are embedded TrueType fonts. No raster artist or external image is used.
No source data is modified.

Run from the article directory:
    python3 code/make_figures.py

Optional raster previews for visual QA can be written outside the package:
    python3 code/make_figures.py --preview-dir /tmp/partition-figure-preview

The default input is data/boltzmann_samples.csv together with data/checks.json.
Outputs are figures/variance_transition.pdf and figures/boltzmann_ecdfs.pdf.
The empirical CDFs use every recorded sample at every t, including ties.
The figure explicitly identifies these as finite-row, unconditioned Boltzmann
experiments. CDF agreement is a diagnostic, not a proof or error certificate.

V_alpha is evaluated from the one-dimensional integral in the article at
40 decimal digits. Its alpha=0 value is independently checked at 55 digits
against both the closed formula and checks.json. The removable values at
alpha=1/2 and theta=0 are inserted from their exact limiting formulas.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import LogLocator, NullFormatter
import mpmath as mp
import numpy as np

CSTAR = 1 - math.pi/4
COLORS = ("#0072B2", "#D55E00", "#009E73")
INK = "#202A36"
GRID = "#CDD3DA"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def va(alpha):
    """The unnormalized subcritical variance, for 0 <= alpha < 1/2."""
    alpha = mp.mpf(alpha)
    require(0 <= alpha < mp.mpf(".5"), "V_alpha requires 0 <= alpha < 1/2")
    bracket = (
        mp.expm1((alpha+mp.mpf(".5"))*mp.log(2))/(2*alpha+1)
        - mp.quad(
            lambda r: (r*(1-r))**(1-alpha)
            * (r*r+(1-r)*(1-r))**(alpha-mp.mpf(".5")),
            [0, mp.mpf(".5"), 1],
        )
    )
    return mp.gamma(mp.mpf(".5")-alpha)*bracket


def normalized_va(alpha):
    """Stable evaluation of (1-2 alpha) V_alpha, including its endpoint."""
    alpha = mp.mpf(alpha)
    require(0 <= alpha <= mp.mpf(".5"), "Normalized V requires 0 <= alpha <= 1/2")
    if alpha == mp.mpf(".5"):
        return 1-mp.pi/4
    bracket = (
        mp.expm1((alpha+mp.mpf(".5"))*mp.log(2))/(2*alpha+1)
        - mp.quad(
            lambda r: (r*(1-r))**(1-alpha)
            * (r*r+(1-r)*(1-r))**(alpha-mp.mpf(".5")),
            [0, mp.mpf(".5"), 1],
        )
    )
    return 2*mp.gamma(mp.mpf("1.5")-alpha)*bracket


def moving_window(theta):
    """W(theta)=c_star (exp(2 theta)-exp(theta))/(2 theta), W(0)=c_star/2."""
    theta = np.asarray(theta, dtype=float)
    result = np.empty_like(theta)
    nonzero = theta != 0
    result[nonzero] = (
        CSTAR*np.exp(theta[nonzero])*np.expm1(theta[nonzero])
        /(2*theta[nonzero])
    )
    result[~nonzero] = CSTAR/2
    return result


def set_style():
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 9,
        "axes.labelsize": 9,
        "axes.titlesize": 9.2,
        "axes.titleweight": "medium",
        "axes.edgecolor": "#5D6875",
        "axes.labelcolor": INK,
        "text.color": INK,
        "xtick.color": INK,
        "ytick.color": INK,
        "xtick.labelsize": 8,
        "ytick.labelsize": 8,
        "axes.linewidth": 0.7,
        "xtick.major.width": 0.6,
        "ytick.major.width": 0.6,
        "xtick.major.size": 3,
        "ytick.major.size": 3,
        "legend.fontsize": 8,
        "legend.frameon": False,
        "mathtext.fontset": "dejavusans",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "savefig.facecolor": "white",
        "figure.facecolor": "white",
        "path.simplify": False,
    })


def clean_axes(ax):
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.grid(axis="y", color=GRID, linewidth=0.55, alpha=0.72)
    ax.set_axisbelow(True)


def save_figure(fig, destination, title, preview_dir):
    fig.savefig(destination, format="pdf", metadata={
        "Title": title,
        "Author": "",
        "Subject": "Partition multiplicity occupancy; mathematical and finite-data figures",
        "Creator": "Matplotlib; reproducible source code in code/make_figures.py",
        "CreationDate": None,
        "ModDate": None,
    })
    if preview_dir is not None:
        preview_dir.mkdir(parents=True, exist_ok=True)
        fig.savefig(preview_dir/(destination.stem+".png"), dpi=190)
    plt.close(fig)


def figure_transition(destination, preview_dir):
    alpha = np.linspace(0, 0.5, 161)
    with mp.workdps(40):
        normalized = np.asarray([float(normalized_va(str(a))) for a in alpha])
    theta = np.linspace(-3, 3, 601)
    window = moving_window(theta)

    fig, axes = plt.subplots(1, 2, figsize=(7.25, 2.95))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.22,
                        top=0.86, wspace=0.38)
    left, right = axes
    clean_axes(left)
    clean_axes(right)

    left.plot(alpha, normalized, color=COLORS[0], linewidth=1.8)
    left.axhline(CSTAR, color="#687482", linewidth=0.95, linestyle=(0, (4, 3)))
    left.scatter([0.5], [CSTAR], s=24, color=COLORS[0], zorder=5, clip_on=False)
    left.set_xlim(0, 0.5)
    left.set_ylim(0.198, 0.361)
    left.set_xticks(np.linspace(0, 0.5, 6))
    left.set_yticks([0.20, 0.25, 0.30, 0.35])
    left.set_xlabel(r"$\alpha$")
    left.set_ylabel(r"$(1-2\alpha)V_\alpha$")
    left.set_title("(a) Approach to the critical pole", loc="left", pad=10)
    left.text(0.035, 0.12, r"$c_*=1-\pi/4$", transform=left.transAxes,
              color="#586473", fontsize=9, va="bottom",
              bbox={"facecolor": "white", "edgecolor": "none", "pad": 1.0})
    left.text(0.96, 0.91, r"$\mathrm{Var}_t(D_\alpha)\sim "
              r"V_\alpha t^{-\alpha-1/2}$", transform=left.transAxes,
              fontsize=8.3, va="top", ha="right")

    right.plot(theta, window, color=COLORS[1], linewidth=1.8)
    right.set_yscale("log")
    right.set_xlim(-3, 3)
    right.set_ylim(1.1e-3, 24)
    right.set_xticks(np.arange(-3, 4))
    right.yaxis.set_major_locator(LogLocator(base=10, numticks=5))
    right.yaxis.set_minor_locator(LogLocator(base=10, subs=[2, 5], numticks=12))
    right.yaxis.set_minor_formatter(NullFormatter())
    right.set_xlabel(r"$\theta$")
    right.set_ylabel(r"$W(\theta)$  (log scale)")
    right.set_title("(b) Variance in the moving window", loc="left", pad=10)
    right.text(0.035, 0.95,
               r"$W(\theta)=c_*\frac{e^{2\theta}-e^\theta}{2\theta}$",
               transform=right.transAxes, fontsize=9, va="top",
               bbox={"facecolor": "white", "edgecolor": "none", "pad": 1.0})
    right.scatter([0], [CSTAR/2], s=25, color=INK, zorder=6)
    right.annotate(r"$W(0)=c_*/2$", xy=(0, CSTAR/2), xytext=(0.45, 0.022),
                   textcoords="data", fontsize=8.7, color=INK,
                   arrowprops={"arrowstyle": "-", "linewidth": 0.65,
                               "color": "#707984"},
                   bbox={"facecolor": "white", "edgecolor": "none", "pad": 1.0})
    fig.text(0.785, 0.035,
             r"$\alpha_n=\frac{1}{2}+\theta/\log(1/\tau_n)$",
             ha="center", fontsize=8.5, color="#586473")
    save_figure(fig, destination,
                "Variance pole and logarithmic moving-window variance", preview_dir)


def read_samples(path):
    grouped = {}
    with path.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream):
            t = float(row["t"])
            group = grouped.setdefault(t, {"Z0_leading": [], "Z1_standard_Gumbel": []})
            for key in group:
                group[key].append(float(row[key]))
    require(sorted(grouped) == [1e-6, 1e-5, 1e-4], "Expected all three recorded t values")
    require(all(len(grouped[t]["Z0_leading"]) > 0 for t in grouped), "No samples")
    return grouped


def draw_ecdf(ax, values, limits, color, label):
    """Ties are aggregated without dropping any sample or changing its weight."""
    x, counts = np.unique(np.asarray(values, dtype=float), return_counts=True)
    cumulative = np.cumsum(counts)/sum(counts)
    xp = np.concatenate(([limits[0]], x, [limits[1]]))
    yp = np.concatenate(([0.0], cumulative, [1.0]))
    return ax.step(xp, yp, where="post", color=color, linewidth=0.9,
                   alpha=0.95, label=label)[0]


def figure_ecdfs(destination, preview_dir, grouped, v0):
    fig, axes = plt.subplots(1, 2, figsize=(7.25, 3.38))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.28,
                        top=0.80, wspace=0.29)
    keys = ("Z0_leading", "Z1_standard_Gumbel")
    labels = (
        r"$t^{1/4}(D_0-\sqrt{\pi/t})$",
        r"$tD_1-\frac{1}{2}\log(1/t)-\frac{3-3\gamma}{2}$",
    )
    titles = ("(a) Unweighted Gaussian limit", "(b) Weight-one Gumbel limit")
    time_order = [1e-4, 1e-5, 1e-6]
    sizes = [len(grouped[t]["Z0_leading"]) for t in time_order]
    require(len(set(sizes)) == 1, "Figure title requires equal sample counts")
    fig.suptitle(f"Finite-row Boltzmann samples: {sizes[0]:,} draws at each t",
                 y=0.98, fontsize=10.1, color=INK)
    legend_handles = []

    for column, (ax, key, label, title) in enumerate(zip(axes, keys, labels, titles)):
        clean_axes(ax)
        all_values = np.concatenate([np.asarray(grouped[t][key]) for t in time_order])
        span = float(np.max(all_values)-np.min(all_values))
        limits = (float(np.min(all_values)-0.045*span),
                  float(np.max(all_values)+0.045*span))
        ax.set_xlim(limits)
        ax.set_ylim(-0.025, 1.025)
        ax.set_yticks(np.linspace(0, 1, 6))
        ax.set_xlabel(label, labelpad=7)
        ax.set_title(title, loc="left", pad=8)
        ax.set_ylabel("Cumulative probability" if column == 0 else "")
        x = np.linspace(limits[0], limits[1], 650)
        if key == "Z0_leading":
            theoretical = np.asarray([
                0.5*(1+math.erf(value/math.sqrt(2*v0))) for value in x
            ])
            theory_label = r"$N(0,V_0)$"
        else:
            theoretical = np.exp(-np.exp(-x))
            theory_label = "Standard Gumbel"
        ax.plot(x, theoretical, color=INK, linewidth=1.6,
                linestyle=(0, (5, 3)), label=theory_label, zorder=6)
        for index, (t, color) in enumerate(zip(time_order, COLORS)):
            handle = draw_ecdf(ax, grouped[t][key], limits, color,
                               rf"$t=10^{{{int(round(math.log10(t)))}}}$")
            if column == 0:
                legend_handles.append(handle)
        ax.text(0.97, 0.06, "Dashed: "+theory_label, transform=ax.transAxes,
                ha="right", va="bottom", fontsize=8.2, color=INK,
                bbox={"facecolor": "white", "edgecolor": "none", "pad": 1.5})
    fig.legend(handles=legend_handles, loc="lower center",
               bbox_to_anchor=(0.52, 0.065), ncol=3,
               handlelength=2.7, columnspacing=2.3)
    fig.text(0.52, 0.018,
             r"$J=\lceil40/\sqrt{t}\rceil$; unconditioned, finite-row experiments; "
             "every sample retained",
             ha="center", fontsize=7.9, color="#586473")
    save_figure(fig, destination,
                "Empirical CDFs from finite-row Boltzmann experiments", preview_dir)


def main():
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, default=root/"data")
    parser.add_argument("--figure-dir", type=Path, default=root/"figures")
    parser.add_argument("--preview-dir", type=Path)
    args = parser.parse_args()
    sample_path = args.data_dir/"boltzmann_samples.csv"
    check_path = args.data_dir/"checks.json"
    old_hashes = {p: hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in (sample_path, check_path)}
    checks = json.loads(check_path.read_text(encoding="utf-8"))
    with mp.workdps(55):
        independent = va(0)
        closed = mp.sqrt(mp.pi)*(mp.sqrt(2)-mp.mpf(3)/4
                  -3*mp.sqrt(2)/8*mp.log(1+mp.sqrt(2)))
        recorded = mp.mpf(checks["analytic"]["V0_closed"])
        require(abs(independent-closed) < mp.mpf("1e-45"),
                "Integral V0 disagrees with its closed expression")
        require(abs(independent-recorded) < mp.mpf("1e-45"),
                "Integral V0 disagrees with the independently recorded check")
        require(abs(normalized_va(mp.mpf(".5"))-(1-mp.pi/4)) < mp.mpf("1e-50"),
                "Incorrect critical endpoint")
        print("Verified V0 =", mp.nstr(independent, 48))
    require(abs(float(moving_window(np.array([0.0]))[0])-CSTAR/2) < 1e-15,
            "Incorrect W(0)")
    grouped = read_samples(sample_path)
    set_style()
    args.figure_dir.mkdir(parents=True, exist_ok=True)
    figure_transition(args.figure_dir/"variance_transition.pdf", args.preview_dir)
    figure_ecdfs(args.figure_dir/"boltzmann_ecdfs.pdf", args.preview_dir,
                 grouped, float(independent))
    for path, old_hash in old_hashes.items():
        require(hashlib.sha256(path.read_bytes()).hexdigest() == old_hash,
                "Input data changed while creating figures")
    print("Wrote two vector PDFs; input data unchanged.")
    print("Matplotlib", matplotlib.__version__, "NumPy", np.__version__,
          "mpmath", mp.__version__)


if __name__ == "__main__":
    main()
