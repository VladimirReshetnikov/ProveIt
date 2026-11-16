#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
import math
from pathlib import Path
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("vhc", ROOT / "tools/verify_hat_certificate.py")
mod = importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name] = mod
assert spec.loader is not None
spec.loader.exec_module(mod)

def euclid(q):
    return float(q[0]), math.sqrt(3.0) * float(q[1])

def add_poly(ax, pts, **kw):
    poly = Polygon([euclid(q) for q in pts], closed=True, fill=False, **kw)
    ax.add_patch(poly)

hat_data = __import__('json').loads((ROOT/'certificates/hat_data.json').read_text())
verts = [tuple(map(int,q)) for q in hat_data['hat_vertices_axial']]
hat = [mod.axial(u,v) for u,v in verts]

fig, ax = plt.subplots(figsize=(6.2,4.8))
add_poly(ax, hat, linewidth=2)
for i,q in enumerate(hat):
    x,y=euclid(q)
    ax.text(x,y,str(i),fontsize=8,ha='center',va='center')
ax.set_aspect('equal')
ax.autoscale_view()
ax.set_xlabel(r'$e_0=(1,0)$ coordinate')
ax.set_ylabel(r'Euclidean $y$')
ax.set_title('The 13-vertex hat in the triangular-lattice basis')
fig.tight_layout()
fig.savefig(ROOT/'figures/hat_outline.pdf')
fig.savefig(ROOT/'figures/hat_outline.png',dpi=180)
plt.close(fig)

# Show the first four exact H outlines after recentering.
tiles = mod.initial_geometries(verts)
levels = [tiles[0]]
for _ in range(4):
    patch,_ = mod.construct_patch(tiles)
    tiles = mod.construct_metatiles(patch)
    levels.append(tiles[0])

fig, ax = plt.subplots(figsize=(7.2,6.0))
for lev,g in enumerate(levels):
    pts=[euclid(q) for q in g.shape]
    # Normalize each around a common origin but with logarithmic scale compression for legibility.
    scale = 1.0 / (2.55**lev)
    pts=[(scale*x,scale*y) for x,y in pts]
    poly=Polygon(pts,closed=True,fill=False,linewidth=1.2,label=f'level {lev}')
    ax.add_patch(poly)
ax.set_aspect('equal')
ax.autoscale_view()
ax.legend()
ax.set_title('Normalized exact H-supertiles (shape convergence)')
ax.set_xlabel('normalized x')
ax.set_ylabel('normalized y')
fig.tight_layout()
fig.savefig(ROOT/'figures/H_supertiles.pdf')
fig.savefig(ROOT/'figures/H_supertiles.png',dpi=180)
plt.close(fig)

# Plot exact cross-slack growth from generated CSV.
import csv
rows=list(csv.DictReader((ROOT/'generated/exact_geometry_stats.csv').open()))
xs=[int(r['level']) for r in rows]
ys=[float(r['minimum_cross_slack_decimal']) for r in rows]
fig, ax = plt.subplots(figsize=(6.4,4.5))
ax.semilogy(xs,ys,marker='o')
ax.set_xlabel('substitution level')
ax.set_ylabel('minimum exact cross-product slack (log scale)')
ax.set_title('Certified strict containment of the distinguished H-child')
ax.grid(True)
fig.tight_layout()
fig.savefig(ROOT/'figures/containment_growth.pdf')
fig.savefig(ROOT/'figures/containment_growth.png',dpi=180)
plt.close(fig)

print('wrote figures')
