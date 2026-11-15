#!/usr/bin/env python3
"""Reproduce the exact-test illustrations as vector PDF and preview PNG.

The geometry and certified path are read from the executable test fixtures.
All geometry decisions remain exact; conversion to float occurs only when
passing coordinates to matplotlib for drawing.

Run from the package root: python3 artifacts/make_figures.py
Requires matplotlib (the mathematical kernel itself uses only the stdlib).
"""

from fractions import Fraction as Q
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Polygon

from jordan_kernel import boundary_cycles, center, hexagon, point, polygon_flood


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = ROOT / "figures"
OUT.mkdir(exist_ok=True)

CURVE = "#172838"
ROUTE = "#087D94"
SEPARATOR = "#C95724"
PALE = "#E7F1F4"
GRID = "#B6CBD2"
INK = "#233342"


def xy(points):
    return [(float(p[0]),float(p[1])) for p in points]


def closed_xy(points):
    pp = xy(points + points[:1])
    return [p[0] for p in pp],[p[1] for p in pp]


def endpoint(ax, p, label, offset, color=ROUTE):
    x,y = map(float,p)
    ax.plot(x,y,"o",ms=6.5,mec="white",mew=1.5,color=color,zorder=8)
    ax.annotate(label,(x,y),xytext=offset,textcoords="offset points",
                fontsize=10.5,color=INK,fontweight="medium",zorder=9,
                bbox={"boxstyle":"round,pad=0.18","facecolor":"white",
                      "edgecolor":"none","alpha":0.95})


def main():
    evidence = json.loads((HERE / "test_results.json").read_text())
    cases = {c["name"]:c for c in evidence["connections"]}
    ucase = cases["concave_left_to_right"]
    scase = cases["square_inside_to_outside"]
    assert evidence["checks_passed"] >= 142
    assert ucase["path_clearance_linf"] == "1/8"
    assert (scase["source_parity"],scase["target_parity"]) == (1,0)

    concave = [point(-3,-3),point(3,-3),point(3,3),point(1,3),
               point(1,-1),point(-1,-1),point(-1,3),point(-3,3)]
    square = [point(-2,-2),point(2,-2),point(2,2),point(-2,2)]
    path = [(Q(p[0]),Q(p[1])) for p in ucase["path"]]
    h = Q(scase["scale"])
    fill = polygon_flood(square,scase["patch_radius"],(0,0),h)
    loops = boundary_cycles(fill.cells,set(fill.parent),h)
    assert [len(p) for p in loops] == scase["boundary_cycle_lengths"]

    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,
                         "pdf.fonttype":42,"ps.fonttype":42,
                         "axes.titlesize":10.5,"axes.titleweight":"semibold"})
    fig,axes = plt.subplots(1,2,figsize=(8.4,4.8),facecolor="white")
    fig.subplots_adjust(left=0.045,right=0.985,top=0.86,bottom=0.16,wspace=0.15)
    fig.suptitle("Finite witnesses in the constructive Jordan argument",
                 x=0.05,ha="left",y=0.975,fontsize=13,fontweight="semibold",color=CURVE)

    ax = axes[0]
    ax.add_patch(Polygon(xy(concave),closed=True,facecolor=PALE,
                         edgecolor=CURVE,linewidth=2.0,zorder=2))
    px,py = zip(*xy(path))
    ax.plot(px,py,color="white",lw=5.0,solid_capstyle="round",zorder=3)
    ax.plot(px,py,color=ROUTE,lw=2.3,solid_capstyle="round",zorder=4)
    ax.plot(px[1:-1],py[1:-1],"o",color=ROUTE,ms=2.2,zorder=5)
    endpoint(ax,path[0],"a",(-16,7))
    endpoint(ax,path[-1],"b",(7,7))
    ax.text(0,1.2,"exterior\nnotch",ha="center",va="center",fontsize=10,
            color="#697B87",linespacing=1.4)
    ax.text(0,-2.17,"24 links\nclearance ≥ 1/8",ha="center",va="center",
            fontsize=10.5,color=ROUTE,
            bbox={"facecolor":PALE,"edgecolor":"none","pad":1})
    ax.set_xlim(-3.45,3.45)
    ax.set_ylim(-3.4,3.45)
    ax.set_title("A  A safe route between the arms",loc="left",pad=12,color=CURVE)

    ax = axes[1]
    # Draw a sparse local collar, and fill exactly the cells reached by BFS.
    for cell in fill.cells:
        c = center(cell,h)
        if abs(c[0]) <= Q(5,2) and abs(c[1]) <= Q(5,2):
            reached = cell in fill.parent
            ax.add_patch(Polygon(xy(hexagon(cell,h)),closed=True,
                                 facecolor=PALE if reached else "white",
                                 edgecolor=GRID,linewidth=0.35,
                                 alpha=1 if reached else 0.55,zorder=1))
    sx,sy = closed_xy(square)
    ax.plot(sx,sy,color=CURVE,lw=2.0,zorder=3)
    for loop in loops:
        bx,by = closed_xy(loop)
        ax.plot(bx,by,color="white",lw=3.6,zorder=4)
        ax.plot(bx,by,color=SEPARATOR,lw=1.9,zorder=5)
    endpoint(ax,center((0,0),h),"a: parity 1",(-32,12))
    endpoint(ax,center((10,0),h),"b: parity 0",(-35,12),SEPARATOR)
    ax.text(0,-0.7,"reached cells",ha="center",color=ROUTE,fontsize=10.5,
            bbox={"facecolor":PALE,"edgecolor":"none","pad":1})
    ax.annotate("106-edge separator",xy=(1.75,-1.7),xytext=(2.3,-2.5),
                fontsize=10,color=SEPARATOR,ha="center",
                arrowprops={"arrowstyle":"-","color":SEPARATOR,"lw":0.8},
                bbox={"facecolor":"white","edgecolor":"none","pad":1.5},zorder=9)
    ax.set_xlim(-2.6,4.35)
    ax.set_ylim(-3.4,3.45)
    ax.set_title("B  A finite separating cycle",loc="left",pad=12,color=CURVE)

    for ax in axes:
        ax.set_aspect("equal",adjustable="box")
        ax.axis("off")

    handles = [Line2D([0],[0],color=CURVE,lw=2,label="given curve"),
               Line2D([0],[0],color=ROUTE,lw=2.3,label="certified route"),
               Line2D([0],[0],color=SEPARATOR,lw=2,label="separating cycle")]
    fig.legend(handles=handles,loc="lower center",bbox_to_anchor=(0.5,0.064),
               ncol=3,frameon=False,handlelength=2.5,columnspacing=2.0,
               labelcolor=INK,fontsize=10)
    fig.text(0.05,0.029,"Exact rational fixtures; distances use the infinity norm.",
             fontsize=9,color="#60717D")

    fig.savefig(OUT / "finite_routes.pdf",bbox_inches="tight",pad_inches=0.13)
    fig.savefig(OUT / "finite_routes.png",dpi=180,bbox_inches="tight",pad_inches=0.13)
    plt.close(fig)
    print(str(OUT / "finite_routes.pdf"))
    print(str(OUT / "finite_routes.png"))


if __name__ == "__main__":
    main()
