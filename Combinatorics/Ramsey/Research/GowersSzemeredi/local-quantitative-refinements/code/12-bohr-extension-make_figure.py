#!/usr/bin/env python3
"""Generate the exact density/boundary feasibility diagram in the article."""
from pathlib import Path
import argparse
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview", type=Path)
    args = parser.parse_args()
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 10.5,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.labelcolor": "#17354a", "text.color": "#17354a",
        "pdf.fonttype": 42, "ps.fonttype": 42,
    })
    fig, ax = plt.subplots(figsize=(6.7, 4.0), layout="constrained")
    eps = np.linspace(0, 1/3, 500)
    kap = (1-3*eps)/2
    ax.fill_between(eps, 0, kap, color="#d7eeeb")
    ax.plot(eps, kap, color="#147d82", linewidth=2.4)
    ratios = np.arange(0, 13)/12
    es = ratios/(2+ratios)
    ks = (1-ratios)/(2+ratios)
    ax.scatter(es, ks, facecolor="#ffffff", edgecolor="#147d82", s=32,
               linewidth=1.2, zorder=5, label="Exact counterexamples on the boundary")
    ax.text(.020, .125, "Extension guaranteed\n$3\\varepsilon+2\\kappa<1$",
            fontsize=12, color="#125d61")
    ax.text(.165, .400, "The theorem makes no\nuniversal guarantee here",
            fontsize=10, color="#546575")
    ax.annotate("$3\\varepsilon+2\\kappa=1$",
                xy=(.17, .245), xytext=(.213, .290),
                arrowprops={"arrowstyle":"-", "color":"#17354a"}, fontsize=11)
    ax.set_xlabel("Missing density $\\varepsilon=|B\\setminus S|/|B|$")
    ax.set_ylabel("Maximum translation loss $\\kappa$")
    ax.set_xlim(-.006, .343)
    ax.set_ylim(0, .525)
    ax.set_xticks([0,1/12,1/6,1/4,1/3], ["0", "$1/12$", "$1/6$", "$1/4$", "$1/3$"])
    ax.set_yticks([0,1/8,1/4,3/8,1/2], ["0", "$1/8$", "$1/4$", "$3/8$", "$1/2$"])
    ax.grid(alpha=.20, linewidth=.6)
    ax.set_axisbelow(True)
    ax.legend(loc="upper right", bbox_to_anchor=(1,1.15), frameon=False, fontsize=9)
    destination = Path(__file__).resolve().with_name("extension_frontier.pdf")
    fig.savefig(destination, metadata={"Title":"Sharp Freiman extension frontier", "Author":"Research article"})
    if args.preview:
        args.preview.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(args.preview, dpi=160)
    plt.close(fig)
    print(destination)


if __name__ == "__main__":
    main()
