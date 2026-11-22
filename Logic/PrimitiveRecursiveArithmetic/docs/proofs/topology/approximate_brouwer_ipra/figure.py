"""Render the N=5 Sperner certificate for the cyclic coordinate map."""
from itertools import combinations
from math import sqrt
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
from matplotlib.patches import Polygon

N = 5
COLORS = ("#176489", "#b34f1d", "#286b50")
MARKERS = ("o", "s", "^")
INK = "#233440"
MUTED = "#52636c"
CELL = ((1, 3), (2, 3), (2, 4))


def gaps(u):
    return (u[0], u[1] - u[0], N - u[1])


def residual(u):
    a = gaps(u)
    return tuple(a[i] - a[(i + 1) % 3] for i in range(3))


def color(u):
    g, a = residual(u), gaps(u)
    return next(i for i in range(3) if g[i] == max(g) and a[i] > 0)


def xy(u):
    _, a1, a2 = gaps(u)
    return ((a1 + a2 / 2) / N, sqrt(3) * a2 / (2 * N))


def main():
    plt.rcParams.update({"font.family": "DejaVu Sans", "mathtext.fontset": "stix",
                         "font.size": 10, "pdf.fonttype": 42})
    fig = plt.figure(figsize=(6.5, 2.48))
    grid = fig.add_axes([0.006, 0.015, 0.478, 0.965], aspect="equal")
    notes = fig.add_axes([0.505, 0.02, 0.483, 0.95])
    for ax in (grid, notes):
        ax.axis("off")

    vertices = [(u, v) for v in range(N + 1) for u in range(v + 1)]
    edges = []
    for u, v in combinations(vertices, 2):
        if sum(abs(a - b) for a, b in zip(gaps(u), gaps(v))) == 2:
            edges.append((xy(u), xy(v)))
    grid.add_collection(LineCollection(edges, colors="#b3c0c6", linewidths=0.75))
    grid.add_patch(Polygon([xy(u) for u in CELL], closed=True, facecolor="#f4ddb0",
                           edgecolor=INK, linewidth=1.6, zorder=2, joinstyle="round"))
    for u in vertices:
        i = color(u)
        grid.scatter(*xy(u), s=36 if i != 2 else 48, marker=MARKERS[i],
                     facecolor=COLORS[i], edgecolor="white", linewidth=0.55, zorder=3)
    grid.scatter(*xy(CELL[0]), s=120, marker="o", facecolor="none",
                 edgecolor=INK, linewidth=1.0, zorder=4)

    for u, label, offset, ha, va in (
        ((N, N), r"$e_0$", (-6, -4), "right", "top"),
        ((0, N), r"$e_1$", (6, -4), "left", "top"),
        ((0, 0), r"$e_2$", (0, 6), "center", "bottom"),
    ):
        grid.annotate(label, xy(u), xytext=offset, textcoords="offset points",
                      ha=ha, va=va, fontsize=12, color=INK)
    grid.set_xlim(-0.115, 1.115)
    grid.set_ylim(-0.105, sqrt(3) / 2 + 0.13)

    notes.set(xlim=(0, 1), ylim=(0, 1))
    notes.text(0.01, 0.91, "Certified cell", color=INK,
               fontsize=12, weight="semibold", va="top")
    columns = (0.08, 0.43, 0.77)
    for x, label in zip(columns, ("Grid vertex $u$", "Color", r"$5(x-q(x))$")):
        notes.text(x, 0.68, label, ha="center", va="center", color=MUTED, fontsize=9)
    notes.plot([0, 0.99], [0.60, 0.60], linewidth=0.65, color="#a7b7c0")
    for row, u in enumerate(CELL):
        y = 0.49 - 0.135 * row
        i = color(u)
        g = ",".join(str(z) for z in residual(u))
        notes.text(columns[0], y, rf"$({u[0]},{u[1]})$", ha="center", va="center",
                   color=INK, fontsize=11)
        notes.scatter(columns[1] - 0.035, y, marker=MARKERS[i], s=27 if i != 2 else 34,
                      facecolor=COLORS[i], edgecolor="none")
        notes.text(columns[1] + 0.032, y, str(i), ha="center", va="center",
                   fontsize=9, color=INK)
        notes.text(columns[2], y, rf"$({g})$", ha="center", va="center",
                   color=INK, fontsize=11)
    notes.text(0.01, 0.052, r"At the ringed anchor,  $\|x-q(x)\|_\infty=1/5$",
               color=INK, fontsize=9.0, va="bottom")
    destination = Path(__file__).with_name("figure.pdf")
    fig.savefig(destination, metadata={"Title": "Sperner certificate on the five-step simplex grid"})
    plt.close(fig)


if __name__ == "__main__":
    main()

