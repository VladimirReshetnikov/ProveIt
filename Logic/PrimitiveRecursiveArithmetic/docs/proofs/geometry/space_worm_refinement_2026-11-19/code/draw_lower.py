"""Draw the explicit inspection polygon and the quadrilateral used in a shadow."""
import sys
import numpy as np
import matplotlib.pyplot as plt
from scipy.spatial import ConvexHull
from matplotlib.patches import Circle, Polygon
from check_inspection import POINTS, SCALE, RADIUS_NUMERATOR

plt.rcParams.update({'font.family': 'DejaVu Sans', 'pdf.fonttype': 42,
                     'font.size': 9, 'axes.titleweight': 'semibold'})
fig, (ax, bx) = plt.subplots(1, 2, figsize=(8.5, 2.55))
teal, border, tan = '#126f70', '#243e4c', '#e9ab77'
v = np.array(POINTS) / SCALE
view = np.array([2., 1., .4])
view /= np.linalg.norm(view)
right = np.cross([0, 0, 1], view)
right /= np.linalg.norm(right)
up = np.cross(view, right)
shadow = v @ np.array([right, up]).T
hull = ConvexHull(shadow)
ax.add_patch(Polygon(shadow[hull.vertices], facecolor='#f3f7f6', edgecolor='#8eaaa9', lw=1))
ax.add_patch(Circle([0, 0], RADIUS_NUMERATOR/SCALE, facecolor='#b9dbd8', edgecolor=teal, lw=1))
ax.plot(*shadow.T, color=border, lw=1.5)
ax.scatter(*shadow[[0,-1]].T, s=13, color='#91451c', zorder=3)
ax.text(0, 0, 'inscribed\nball', ha='center', va='center', color=teal, size=8)
ax.set(xlim=(-.28,.29), ylim=(-.24,.24), aspect='equal', title='A test curve that forces a ball')
ax.axis('off')

O, B, C, F = (0,0), (1,0), (.43,.23), (.58,-.31)
poly = np.array([O, (.11,.12), C, (.77,.16), B, (.85,-.19), F, (.28,-.22)])
bx.add_patch(Polygon(poly, facecolor=tan, edgecolor=border, lw=1.1))
bx.add_patch(Polygon([O,C,B,F], facecolor='#dcecea', edgecolor=teal, lw=1.1))
bx.plot([0,1], [0,0], color=border, lw=.85)
for xy, label, dx, dy in [(O,'$O$',-.035,-.005),(B,'$B$',.035,-.005),(C,'$C$',0,.039),(F,'$F$',0,-.046)]:
    bx.scatter(*xy, color=border, s=11, zorder=3)
    bx.text(xy[0]+dx,xy[1]+dy,label,ha='center',va='center',color=border)
bx.text(.52,.054,'diameter $d$',ha='center',color=teal,size=8)
bx.set(aspect='equal',xlim=(-.12,1.12),ylim=(-.42,.34), title='The diameter quadrilateral in a shadow')
bx.axis('off')
fig.subplots_adjust(wspace=.14, top=.86, bottom=.0, left=.02, right=.98)
fig.savefig(sys.argv[1] if len(sys.argv)>1 else 'lower_geometry.pdf',bbox_inches='tight',pad_inches=.025)
