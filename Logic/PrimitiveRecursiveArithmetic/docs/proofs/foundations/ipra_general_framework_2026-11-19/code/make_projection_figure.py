#!/usr/bin/env python3
"""Illustrate finite-cloud projection through rank collapse.
All selected points are computed with exact fractions; floats are used only
to render the figure. Requires matplotlib in addition to the check suite.
"""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from convex_clouds import hull_cloud, pick, segment_project

plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9})
fig, axes = plt.subplots(1, 3, figsize=(10, 3.5), sharex=True, sharey=True)
anchor = (Q(1,3), Q(1))
for ax, height in zip(axes, [Q(0), Q(1,32), Q(1,4)]):
    vertices = ((Q(-1),Q(0)), (Q(1),Q(0)), (Q(0),height))
    cloud = hull_cloud(vertices, 16)
    selected = pick(cloud, anchor)
    exact = pick([segment_project(anchor,a,b) for a,b in combinations(vertices,2)], anchor)
    vx,vy = zip(*[(float(x),float(y)) for x,y in vertices])
    ax.fill(vx,vy,color='#c9dfed',alpha=.65,zorder=1)
    cx,cy = zip(*[(float(x),float(y)) for x,y in cloud])
    ax.scatter(cx,cy,s=8,color='#647b89',alpha=.6,zorder=2)
    ax.plot([float(anchor[0]),float(exact[0])], [float(anchor[1]),float(exact[1])],
            color='#ba5b42',lw=1.3,zorder=2)
    ax.scatter([float(anchor[0])],[float(anchor[1])],marker='*',s=85,
               color='#ba5b42',zorder=4,label='Anchor')
    ax.scatter([float(exact[0])],[float(exact[1])],s=55,marker='o',
               facecolors='none',edgecolors='#ba5b42',lw=1.6,zorder=5,label='Projection')
    ax.scatter([float(selected[0])],[float(selected[1])],s=38,marker='x',
               color='#123b57',lw=1.5,zorder=6,label='Finite choice')
    ax.set_title('Height '+str(height),fontsize=10,pad=10)
    ax.set_xlim(-1.13,1.13); ax.set_ylim(-.12,1.13)
    ax.set_aspect('equal',adjustable='box')
    ax.set_xticks([-1,0,1]); ax.set_yticks([0,.5,1])
    ax.grid(alpha=.15); ax.spines[['top','right']].set_visible(False)
axes[0].set_ylabel('Second coordinate')
axes[1].set_xlabel('First coordinate')
handles,labels=axes[0].get_legend_handles_labels()
fig.legend(handles,labels,loc='lower center',ncol=3,frameon=False,bbox_to_anchor=(.5,-.02))
fig.subplots_adjust(bottom=.20,wspace=.14,top=.87)
out=Path(__file__).resolve().parents[1]/'paper'/'figures'
out.mkdir(parents=True,exist_ok=True)
fig.savefig(out/'convex_projection.pdf',bbox_inches='tight')
fig.savefig(out/'convex_projection.png',dpi=180,bbox_inches='tight')
print(out/'convex_projection.pdf')
