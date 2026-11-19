#!/usr/bin/env python3
"""Reproduce arithmetic and figures for the convex space-curve cover report.

The exact rational computations are checks of finite geometry. Plotting,
floating-point quadrature, and random-direction checks are illustrations;
none replaces the mathematical universality proof in report.pdf.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import math

import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from scipy.spatial import ConvexHull

ROOT = Path(__file__).resolve().parents[1]
FIG = ROOT / "figures"
DATA = ROOT / "data"
for directory in (FIG, DATA):
    directory.mkdir(parents=True, exist_ok=True)

mp.mp.dps = 80

def dec(x):
    return mp.nstr(x, 65)

def ff(x):
    return mp.mpf(x.numerator) / x.denominator

normals = [
    (F(-394797,401525), F(-73196,401525)),
    (F(0), F(-1)),
    (F(207,305), F(224,305)),
    (F(1767,4505), F(4144,4505)),
]
offsets = [F(0), F(0), F(130783,250000), F(446199,1000000)]

def intersect(i, j):
    a,b = normals[i]
    c,d = normals[j]
    det = a*d-b*c
    return ((offsets[i]*d-b*offsets[j])/det,
            (a*offsets[j]-offsets[i]*c)/det)

quad = [intersect(0,1), intersect(1,2), intersect(2,3), intersect(3,0)]
for x,y in quad:
    assert all(a*x+b*y <= h for (a,b),h in zip(normals, offsets))
area = sum(quad[i][0]*quad[(i+1)%4][1]-quad[(i+1)%4][0]*quad[i][1]
           for i in range(4))/2
reported_area = F(7170601298323360123534337,29109471743520000000000000)
assert area == reported_area
lifted = F(2,9)*area
assert lifted == F(7170601298323360123534337,130992622845840000000000000)

values = {
    "length_convention": "total rectifiable path length, with multiplicity",
    "spatial_motions": "proper rotations and translations",
    "exact_minimum": "not known; not claimed in this report",
    "main_lower_exact": "3/220",
    "main_lower_decimal": dec(mp.mpf(3)/220),
    "elementary_tetrahedron_lower_exact": "1/(54*sqrt(2))",
    "elementary_tetrahedron_lower_decimal": dec(1/(54*mp.sqrt(2))),
    "helix_lower_exact": "1/(18*pi*sqrt(3))",
    "helix_lower_decimal": dec(1/(18*mp.pi*mp.sqrt(3))),
    "published_theorem_upper_exact": "pi/54",
    "published_theorem_upper_decimal": dec(mp.pi/54),
    "general_lift_factor": "2/9",
    "keller_preprint_planar_area_exact": str(area),
    "keller_preprint_planar_area_decimal": dec(ff(area)),
    "preprint_dependent_spatial_upper_exact": str(lifted),
    "preprint_dependent_spatial_upper_decimal": dec(ff(lifted)),
    "preprint_status": "The area is checked exactly here. The universal-cover theorem and reported Lean certificates were not independently replayed.",
    "historical_2001_explicit_prism_volume": dec((mp.sqrt(3)/12+mp.pi/24)*mp.pi**2/(1+mp.pi**2)**mp.mpf('1.5')),
}
(DATA / "bounds.json").write_text(json.dumps(values, indent=2)+"\n")
(DATA / "keller_quadrilateral.json").write_text(json.dumps({
    "source": "Ethan Keller, arXiv:2609.21968v1, Section 4",
    "normals": [[str(c) for c in n] for n in normals],
    "offsets": [str(h) for h in offsets],
    "vertices": [[str(c) for c in p] for p in quad],
    "area": str(area),
    "spatial_lift_volume": str(lifted),
    "validation_scope": "exact vertex intersections, feasibility, shoelace area, and multiplication by 2/9; not the source's cover certificate",
}, indent=2)+"\n")

plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 10,
    "axes.labelcolor": "#273e53", "text.color": "#182d40",
    "axes.edgecolor": "#a8b7c2", "axes.titleweight": "medium",
    "pdf.fonttype": 42, "ps.fonttype": 42,
})
NAVY, TEAL, GOLD = "#153c59", "#208a96", "#c3862c"

def save(fig, name):
    fig.savefig(FIG / (name+".pdf"), bbox_inches="tight", facecolor="white")
    fig.savefig(FIG / (name+".png"), bbox_inches="tight", dpi=190, facecolor="white")
    plt.close(fig)

def clean3(ax):
    ax.grid(False)
    for axis in (ax.xaxis, ax.yaxis, ax.zaxis):
        axis.pane.set_facecolor((1,1,1,0))
        axis.pane.set_edgecolor((1,1,1,0))
    ax.tick_params(labelsize=8, pad=0)

fig = plt.figure(figsize=(10.0,4.3), layout="constrained")
ax = fig.add_subplot(121, projection="3d")
phi = np.linspace(-np.pi/2, np.pi/2, 120)
theta = np.linspace(-np.pi/12, np.pi/12, 65)
ph, th = np.meshgrid(phi, theta)
ax.plot_surface(np.cos(ph)*np.cos(th), np.cos(ph)*np.sin(th), np.sin(ph)/6,
                color=TEAL, alpha=.84, linewidth=0, antialiased=True, shade=True)
t, ph2 = np.meshgrid(np.linspace(0,1,35), phi)
for angle, color in ((-np.pi/12,NAVY),(np.pi/12,"#77b8c0")):
    r=t*np.cos(ph2)
    ax.plot_surface(r*np.cos(angle),r*np.sin(angle),np.sin(ph2)/6,
                    color=color,alpha=.7,linewidth=0,antialiased=True)
    ax.plot(np.cos(phi)*np.cos(angle),np.cos(phi)*np.sin(angle),np.sin(phi)/6,
            color=NAVY,lw=1.1)
ax.plot([0,0],[0,0],[-1/6,1/6],color=NAVY,lw=1.1)
ax.set_xlim(-.02,1.03); ax.set_ylim(-.3,.3); ax.set_zlim(-.18,.18)
ax.set_box_aspect((1.05,.6,.36))
ax.view_init(elev=23, azim=-57)
ax.set_xlabel("x",labelpad=1); ax.set_ylabel("y",labelpad=1); ax.set_zlabel("z",labelpad=1)
ax.set_title("A convex universal container",pad=10)
clean3(ax)

ax = fig.add_subplot(122)
z=np.linspace(-1/6,1/6,500)
r=np.sqrt(np.maximum(0,1-36*z*z))
ax.fill_betweenx(z,0,r,color=TEAL,alpha=.20)
ax.plot(r,z,color=TEAL,lw=2)
h=.22
ell=math.sqrt(1-9*h*h)
ax.add_patch(plt.Rectangle((0,-h/2),ell,h,facecolor=GOLD,edgecolor=GOLD,alpha=.34,lw=1.4))
ax.plot([ell,ell],[-h/2,h/2],color=GOLD,lw=1.5)
ax.axhline(0,color="#c3cdd5",lw=.7)
ax.text(.18,.132,"Ellipsoid boundary",color=TEAL,fontsize=10)
ax.text(.15,-.014,"One prism contains\nthe whole placed curve",color="#73501c",fontsize=10)
ax.text(.72,-.155,r"$\ell^2+9h^2\leq1$",fontsize=11,ha="center")
ax.set_xlim(0,1.04); ax.set_ylim(-.19,.19)
ax.set_yticks([-1/6,0,1/6], [r"$-1/6$","0",r"$1/6$"])
ax.set_xlabel(r"Radial coordinate $\sqrt{x^2+y^2}$")
ax.set_ylabel("Height z")
ax.set_title("Radial section and the fitting argument")
ax.spines[["top","right"]].set_visible(False)
save(fig,"cover")

vertices=np.array([[3,0,0],[0,3,2],[-3,0,4],[0,-3,6],[3,0,8]],dtype=float)/(4*np.sqrt(22))
hull=ConvexHull(vertices)
fig=plt.figure(figsize=(9.3,4.2),layout="constrained")
ax=fig.add_subplot(121,projection="3d")
polys=[vertices[s] for s in hull.simplices]
ax.add_collection3d(Poly3DCollection(polys,facecolors="#8dc6ca",alpha=.25,edgecolors="#96b5bd",linewidths=.7))
ax.plot(*vertices.T,color=NAVY,lw=2.4,marker="o",markersize=4)
for i,p in enumerate(vertices):
    ax.text(p[0]+.008,p[1],p[2]+.008,str(i),fontsize=9)
mins=vertices.min(axis=0)-.025; maxs=vertices.max(axis=0)+.025
ax.set_xlim(mins[0],maxs[0]); ax.set_ylim(mins[1],maxs[1]); ax.set_zlim(mins[2],maxs[2])
ax.set_box_aspect(maxs-mins)
ax.view_init(elev=20,azim=-10)
ax.set_xticks([-.15,0,.15]); ax.set_yticks([-.15,0,.15]); ax.set_zticks([0,.2,.4])
ax.set_xlabel("x",labelpad=0);ax.set_ylabel("y",labelpad=0);ax.set_zlabel("z",labelpad=0)
ax.set_title("The four-edge unit test curve")
clean3(ax)
ax=fig.add_subplot(122)
B=np.array([[0,0],[1.0,0],[.72,.64],[-.12,.58]])
q=np.array([.35,.2])
ax.fill(B[:,0],B[:,1],color=TEAL,alpha=.16)
ax.plot(np.r_[B[:,0],B[0,0]],np.r_[B[:,1],B[0,1]],color=TEAL,lw=1.8)
for t in (.25,.5,.75):
    smaller=t*q+(1-t)*B
    ax.plot(np.r_[smaller[:,0],smaller[0,0]],np.r_[smaller[:,1],smaller[0,1]],color=GOLD,lw=1.2)
ax.plot(q[0],q[1],"o",color=NAVY,ms=4)
ax.text(q[0]+.025,q[1]-.07,r"$x_0$",fontsize=12)
ax.text(.43,.48,r"$P_uK$",color=TEAL,fontsize=13)
ax.text(.5,-.12,r"$\{f\geq t\}\supseteq t x_0+(1-t)P_uK$",ha="center",fontsize=12)
ax.text(.5,-.25,r"$\mathrm{Vol}(K)\geq\frac{1}{3}\,\mathrm{Area}(P_uK)$",ha="center",fontsize=14)
ax.set_aspect("equal");ax.axis("off")
ax.set_title("A unit segment controls fiber lengths")
save(fig,"lower_bound")

fig=plt.figure(figsize=(7.4,3.7),layout="constrained")
ax=fig.add_subplot(121,projection="3d")
t=np.linspace(0,2*np.pi,300)
rr=1/(np.pi*np.sqrt(6)); hh=1/np.sqrt(3)
pts=np.column_stack([rr*np.cos(t),rr*np.sin(t),hh*t/(2*np.pi)])
ax.plot(*pts.T,color=NAVY,lw=2.1)
ax.plot([rr,rr],[0,0],[0,hh],color=GOLD,lw=1.4,ls="--")
for t0 in np.linspace(0,2*np.pi,9)[1:-1]:
    p=np.array([rr*np.cos(t0),rr*np.sin(t0),hh*t0/(2*np.pi)])
    for a in (pts[0],pts[-1]):
        ax.plot([a[0],p[0]],[a[1],p[1]],[a[2],p[2]],color=TEAL,alpha=.4,lw=.6)
ax.set_box_aspect((2*rr,2*rr,hh));ax.view_init(elev=22,azim=-55)
ax.set_axis_off();ax.set_title("A unit helix")
ax=fig.add_subplot(122)
angles=np.linspace(0,2*np.pi,11)
circle=np.column_stack([np.cos(angles),np.sin(angles)])
ax.plot(np.cos(t),np.sin(t),color=TEAL,lw=1.3)
ax.plot(circle[:,0],circle[:,1],color=NAVY,lw=1.1)
for p in circle[1:-1]:
    ax.plot([1,p[0]],[0,p[1]],color=GOLD,lw=.9,alpha=.8)
ax.plot(1,0,"o",color=NAVY,ms=4)
ax.text(1.05,0,"p",va="center")
ax.set_aspect("equal");ax.axis("off");ax.set_title("Fan triangles in the projection")
save(fig,"helix")

print(json.dumps({"status":"ok","exact_quadrilateral_area":str(area),
                  "main_lower":values["main_lower_decimal"],
                  "main_upper":values["published_theorem_upper_decimal"],
                  "preprint_dependent_upper":values["preprint_dependent_spatial_upper_decimal"],
                  "figures":["cover","lower_bound","helix"]},indent=2))
