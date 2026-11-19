"""Draw the certified routes. Usage: python draw_ico_strips.py [output.pdf]."""
import math
from pathlib import Path
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from matplotlib.lines import Line2D
from matplotlib.patches import Patch
from icosahedron import face, chamber

words = ['T0 T4 T3 U3 V3 W2', 'T0 U0 V1 W0 W1 W2']
fig, axes = plt.subplots(2, 1, figsize=(6.8, 2.9))
fig.subplots_adjust(left=.035, right=.99, top=.98, bottom=.18, hspace=.10)
for i, (ax, word) in enumerate(zip(axes, words)):
    def xy(p):
        u,v = p
        return ((-1 if i == 0 else 1) * float(v + u/2), -float(u) * math.sqrt(3)/2)
    def polygon(points, **kwargs):
        ax.add_patch(Polygon([xy(p) for p in points], closed=True, **kwargs))
    labels = word.split()
    triangle = dict(zip(face(labels[0]), [(0,0), (1,0), (0,1)]))
    src = chamber(triangle,0,1)
    for j, label in enumerate(labels):
        if j:
            vertices = set(face(label))
            shared = vertices & triangle.keys()
            a,b = [triangle[k] for k in shared]
            c, = [p for k,p in triangle.items() if k not in shared]
            new, = vertices - shared
            triangle = {k: triangle[k] for k in shared}
            triangle[new] = (a[0]+b[0]-c[0], a[1]+b[1]-c[1])
        polygon(triangle.values(),facecolor='#f7f8f8', edgecolor='#596778', lw=1)
    dst = chamber(triangle,11,8)
    polygon(src, facecolor='#89b9d1', edgecolor='#316984', lw=1)
    polygon(dst, facecolor='#f1b58f', edgecolor='#995b3a', lw=1)
    segment = [xy(src[0]), xy(dst[0])]
    ax.plot(*zip(*segment), color='#503568', lw=1.65, zorder=3)
    for label,(x,y) in zip(['N','S'],segment):
        ax.plot(x,y,'o', color='#503568', ms=3.6, zorder=4)
        ax.text(x,y+(.06 if label=='N' else -.07), label,
                ha='center',va=('bottom' if label=='N' else 'top'),fontsize=9.5)
    ax.text(-.31,.50,f'Route {i+1}',transform=ax.transAxes,ha='right',va='center',
            fontsize=10.5)
    ax.margins(x=.04,y=.25); ax.autoscale_view()
    ax.set_aspect('equal');ax.axis('off')
fig.legend(handles=[Patch(facecolor='#89b9d1',edgecolor='#316984',label='Source chamber'),
                    Patch(facecolor='#f1b58f',edgecolor='#995b3a',label='Antipodal chamber'),
                    Line2D([0],[0],color='#503568',lw=1.65,label='Vertex-to-vertex path')],
           loc='lower center',bbox_to_anchor=(.52,.012),ncol=3,frameon=False,fontsize=8.5)
out = Path(sys.argv[1]) if len(sys.argv)>1 else Path('ico_strips.pdf')
fig.savefig(out, bbox_inches='tight', pad_inches=.05)
