"""Render the quadrilateral-based universal cover and its exact section profile."""
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import to_rgb
from matplotlib.patches import Polygon, Rectangle
import numpy as np

from check_bounds import HEIGHT, centered_vertices

H = float(HEIGHT)
BASE = np.array(centered_vertices(), dtype=float)
NAVY = "#17344a"
TEAL = "#127e80"
ORANGE = "#b55222"


def scale(z):
    return np.sqrt(np.maximum(0, 1 - 36*z*z))


def draw_body(ax):
    camera = np.array([1.45, -2.5, 1.35])
    camera /= np.linalg.norm(camera)
    right = np.cross([0, 0, 1], camera)
    right /= np.linalg.norm(right)
    up = np.cross(camera, right)
    screen = np.array([right, up]).T
    levels = np.linspace(-H/2, H/2, 101)
    rings = [np.column_stack((scale(z)*BASE, np.full(4, z))) for z in levels]
    faces = []
    light = np.array([-.2, -.65, .73])
    for k, (lower, upper) in enumerate(zip(rings, rings[1:])):
        for i in range(4):
            j = (i + 1) % 4
            quad = np.array([lower[i], lower[j], upper[j], upper[i]])
            normal = np.cross(quad[1]-quad[0], quad[3]-quad[0])
            normal /= np.linalg.norm(normal)
            if normal @ camera > 0:
                bright = .16 + .54 * max(0, normal @ light)
                color = (1-bright)*np.array(to_rgb("#087b80")) + bright*np.ones(3)
                faces.append((quad.mean(axis=0)@camera, quad, color))
    faces.append((rings[-1].mean(axis=0)@camera, rings[-1], "#b9e2dc"))
    for _, poly, color in sorted(faces, key=lambda entry: entry[0]):
        ax.add_patch(Polygon(poly@screen, facecolor=color, edgecolor=color, lw=.7))
    for ring in [rings[len(rings)//2], rings[-1]]:
        for i in range(4):
            j = (i+1) % 4
            side = ring[j]-ring[i]
            if ring is rings[-1] or np.cross(side, [0,0,1]) @ camera >= 0:
                xy = ring[[i,j]]@screen
                ax.plot(*xy.T, color=TEAL, lw=.85)
    points = np.vstack(rings) @ screen
    ax.set(xlim=(points[:,0].min()-.035, points[:,0].max()+.035),
           ylim=(points[:,1].min()-.022, points[:,1].max()+.022), aspect="equal")
    ax.axis("off")


def draw_profile(ax):
    z = np.linspace(-H/2, H/2, 500)
    ax.fill_betweenx(z, 0, scale(z), color="#d9eee9")
    ax.plot(scale(z), z, color=TEAL, lw=1.7)
    for zz in (-H/2, H/2):
        ax.plot([0, scale(zz)], [zz,zz], color=TEAL, lw=1.4)
    span = .19
    half = span/2
    prism_scale = scale(half)
    ax.add_patch(Rectangle((0,-half), prism_scale, span,
                           fc="#b5522219", ec=ORANGE, lw=1.2, zorder=3))
    ax.text(.39, 0, "fitting prism", fontsize=9, color="#754025", ha="center", va="center")
    ax.set(xlim=(0,1.04), ylim=(-.17,.17),
           xticks=[0,.5,1], xticklabels=["0","0.5","1"],
           yticks=[-H/2,0,H/2], yticklabels=[r"$-2/13$","0",r"$2/13$"])
    ax.set_xlabel("Horizontal scale", fontsize=9, color=NAVY)
    ax.set_ylabel("Height  $z$", fontsize=9, color=NAVY)
    ax.tick_params(colors=NAVY, labelsize=8, length=3)
    for name, spine in ax.spines.items():
        spine.set_visible(name in ("bottom","left"))
        spine.set_color("#87999d")


def main():
    plt.rcParams.update({"font.family":"DejaVu Sans", "pdf.fonttype":42})
    fig = plt.figure(figsize=(7.05, 2.55))
    left = fig.add_axes([.015,.10,.53,.83])
    right = fig.add_axes([.666,.245,.30,.65])
    draw_body(left)
    draw_profile(right)
    fig.savefig(Path(__file__).with_name("cover_figure.pdf"), bbox_inches="tight",
                pad_inches=.035)
    plt.close(fig)


if __name__ == "__main__":
    main()
