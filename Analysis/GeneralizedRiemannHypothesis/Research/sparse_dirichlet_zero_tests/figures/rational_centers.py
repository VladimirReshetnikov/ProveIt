"""Draw the six sampling rays in the upper half-plane. Requires Matplotlib."""
from math import cos, pi, sin, sqrt
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Arc


def main():
    plt.rcParams.update({
        "font.family": "DejaVu Serif",
        "mathtext.fontset": "dejavuserif",
        "pdf.fonttype": 42,
        "font.size": 10,
    })
    teal, rust, ink, axis = "#116668", "#A3421A", "#20333F", "#829097"
    height = sqrt(3)
    fig, ax = plt.subplots(figsize=(5.85, 2.35))
    ax.set_aspect("equal", adjustable="box")
    ax.set_xlim(-3.38, 3.38)
    ax.set_ylim(-0.40, 2.22)
    ax.set_axis_off()
    ax.plot([-3.34, 3.34], [0, 0], color=axis, lw=0.9, zorder=1)
    for center in (-3, -1, 0, 1, 3):
        ax.plot([0, center], [height, 0], color=teal, lw=1.55, zorder=2)
        ax.scatter(center, 0, color=teal, s=24, zorder=3)
        ax.annotate(f"${center}$", (center, 0), xytext=(0, -5),
                    textcoords="offset points", ha="center", va="top", color=ink)
    ax.plot([0, 2], [height, 0], color=rust, lw=1.55,
            linestyle=(0, (3.4, 2.0)), zorder=3)
    ax.scatter(2, 0, marker="D", s=26, color=rust, zorder=4)
    ax.annotate("$c=2$", (2, 0), xytext=(0, -5), textcoords="offset points",
                ha="center", va="top", color=rust)
    radius = 0.63
    ax.add_patch(Arc((0, height), 2*radius, 2*radius, theta1=210, theta2=240,
                     color=teal, lw=0.9))
    ax.text(0.98*cos(5*pi/4), height+0.98*sin(5*pi/4), r"$\pi/6$",
            color=teal, ha="center", va="center", fontsize=9)
    ax.scatter(0, height, s=30, color=ink, zorder=5)
    ax.annotate(r"$w=i\sqrt{3}$", (0, height), xytext=(0, 6),
                textcoords="offset points", color=ink, ha="center", va="bottom")
    fig.subplots_adjust(left=0.01, right=0.99, top=0.99, bottom=0.01)
    fig.savefig(Path(__file__).with_suffix(".pdf"),
                metadata={"Title": "Exceptional rational sampling centers"})
    plt.close(fig)


if __name__ == "__main__":
    main()
