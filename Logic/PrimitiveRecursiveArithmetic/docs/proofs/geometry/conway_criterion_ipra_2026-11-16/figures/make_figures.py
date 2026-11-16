#!/usr/bin/env python3
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
import sys

import matplotlib.pyplot as plt
from matplotlib.patches import Polygon as MplPolygon

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))
from conway_core import load_datum, halfturn_point  # noqa: E402

EXAMPLE = ROOT / "examples" / "zigzag_conway_tile.json"
OUT = ROOT / "figures"

tile = load_datum(EXAMPLE)
poly = tile.boundary_polygon()
t = tile.t
u = tile.u
s = tile.e_center2


def fpoint(p):
    return float(p[0]), float(p[1])


def shifted(points, n, k, half=False):
    lam = (n * t[0] + k * u[0], n * t[1] + k * u[1])
    if half:
        points = tuple(halfturn_point(p, s) for p in points)
    return [(float(p[0] + lam[0]), float(p[1] + lam[1])) for p in points]


def save(fig, stem):
    fig.savefig(OUT / f"{stem}.pdf", bbox_inches="tight")
    fig.savefig(OUT / f"{stem}.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


# Figure 1: one tile, its marked boundary points and period vectors.
fig, ax = plt.subplots(figsize=(8.5, 6.2))
ax.add_patch(MplPolygon([fpoint(p) for p in poly], closed=True, alpha=0.22, edgecolor="black", linewidth=2))
for path, label in zip(tile.paths(), "abcdef"):
    xy = [fpoint(p) for p in path]
    ax.plot([p[0] for p in xy], [p[1] for p in xy], linewidth=2.4, label=label)
for name, p in zip("ABCDEF", tile.marked):
    x, y = fpoint(p)
    ax.scatter([x], [y], s=28, zorder=5)
    ax.text(x + 0.12, y + 0.12, name, fontsize=11, weight="bold")
A = tile.A
ax.arrow(float(A[0]), float(A[1]), float(t[0]), float(t[1]), width=0.025, length_includes_head=True)
ax.text(float(A[0] + t[0] / 2), float(A[1] + t[1] / 2), r"$t$", fontsize=12)
ax.arrow(float(A[0]), float(A[1]), float(u[0]) * 0.34, float(u[1]) * 0.34, width=0.025, length_includes_head=True)
ax.text(float(A[0] + u[0] * Fraction(17,100)), float(A[1] + u[1] * Fraction(17,100)), r"$0.34u$", fontsize=11)
ax.set_aspect("equal")
ax.set_title("A polygonal Conway datum with six boundary paths")
ax.grid(True, linewidth=0.35)
ax.legend(ncol=3, loc="upper right", title="boundary path")
save(fig, "zigzag_conway_tile")

# Figure 2: finite window of the two-orbit periodic tiling.
fig, ax = plt.subplots(figsize=(10.5, 7.0))
for n in range(-3, 4):
    for k in range(-3, 4):
        for half, alpha in ((False, 0.42), (True, 0.28)):
            xy = shifted(poly, n, k, half=half)
            patch = MplPolygon(xy, closed=True, alpha=alpha, edgecolor="black", linewidth=0.65)
            ax.add_patch(patch)
ax.set_xlim(-18, 18)
ax.set_ylim(-12, 24)
ax.set_aspect("equal")
ax.set_title(r"Two tile orbits $T+nt+ku$ and $H_e(T)+nt+ku$")
ax.set_xlabel(r"periods $t=(1,6)$ and $u=(-11,7)$")
ax.grid(True, linewidth=0.25)
save(fig, "zigzag_conway_tiling")

print("wrote figure PDFs and PNGs")
