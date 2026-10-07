#!/usr/bin/env python3
"""Reproduce explanatory figures; no floating-point result is used as proof."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "figures"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 9,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.labelcolor": "#17354d",
    "text.color": "#17354d",
    "axes.edgecolor": "#8596a1",
    "xtick.color": "#536675",
    "ytick.color": "#536675",
    "pdf.fonttype": 42,
    "savefig.bbox": "tight",
})
BLUE = "#147d85"
GRAY = "#71818f"
ORANGE = "#b75a27"


def local_bounds():
    # The source-12 fixed-constant sparse branch applies up to alpha = 1/6.
    alpha = np.geomspace(1e-4, 1/6, 360)
    p = np.log(2)**2 / (np.log(32/alpha)*np.log(32/alpha**2))
    retained = alpha*p/20
    old_retained = alpha**5/20000
    radius = np.log(2)**2*alpha**5/(3*2.0**69*np.pi*(1+alpha)**2)
    old_radius = alpha**19/(3*np.pi*2.0**149)
    fig, axes = plt.subplots(1, 2, figsize=(6.5, 2.85), layout="constrained")
    for ax, new, old, title, ylabel in zip(
        axes, (retained, radius), (old_retained, old_radius),
        ("Retained fraction", "Bohr radius"),
        ("Guaranteed fraction of the domain", "Guaranteed inner radius"),
    ):
        ax.loglog(alpha, new, color=BLUE, lw=2, label="Present theorem")
        ax.loglog(alpha, old, color=GRAY, lw=1.8, ls="--", label="Source 12")
        ax.set_title(title, loc="left", fontweight="bold", fontsize=10)
        ax.set_xlabel(r"Domain density $\alpha$")
        ax.set_ylabel(ylabel, fontsize=8)
        ax.set_xlim(alpha[0], alpha[-1])
        ax.grid(axis="both", which="major", alpha=0.15)
    axes[0].legend(loc="upper left", frameon=False, fontsize=8)
    fig.savefig(OUT / "local_bounds.pdf")
    plt.close(fig)


def harmonic_ratio():
    coefficients = np.array([
        222, 864, 4080, 9120, 25640, 31808, 55120, 49280,
        52360, 28320, 24160, 4256, 5920, 0, 0, 0, 222,
    ], dtype=float)
    b = np.linspace(-0.27, 0.09, 650)
    ratio = np.polynomial.polynomial.polyval(b, coefficients)/(16*(1+b**4)**4)
    witness_b = -1/7
    witness_ratio = 1366299579065739/133153321267264
    fig, ax = plt.subplots(figsize=(6.25, 2.85), layout="constrained")
    ax.plot(b, ratio, color=BLUE, lw=2)
    ax.axhline(111/8, color=GRAY, ls="--", lw=1.3)
    ax.scatter([witness_b, 0], [witness_ratio, 111/8],
               color=[ORANGE, GRAY], s=30, zorder=4)
    ax.annotate(r"$b=-1/7$: exact certificate" + "\n" + r"$R_4=10.261100\ldots$",
                (witness_b, witness_ratio), xytext=(-0.252, 11.7),
                fontsize=8, arrowprops={"arrowstyle": "-", "color": ORANGE},
                color=ORANGE)
    ax.annotate(r"Single cosine: $111/8$",
                (0, 111/8), xytext=(-0.075, 14.55), fontsize=8, color=GRAY)
    ax.set(xlabel=r"Third-harmonic coefficient $b$",
           ylabel=r"$R_4(b)=\|f_b\|_{U^4}^{16}/\|f_b\|_{U^2}^{16}$",
           xlim=(b[0], b[-1]))
    ax.set_title("A negative third harmonic improves the ratio",
                 loc="left", fontweight="bold", fontsize=10)
    ax.grid(alpha=0.15)
    fig.savefig(OUT / "two_harmonic_ratio.pdf")
    plt.close(fig)


if __name__ == "__main__":
    local_bounds()
    harmonic_ratio()
    print("Wrote figures/local_bounds.pdf and figures/two_harmonic_ratio.pdf")
