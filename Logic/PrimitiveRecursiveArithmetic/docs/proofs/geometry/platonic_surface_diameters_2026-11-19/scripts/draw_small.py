"""Draw the fundamental tetrahedral and octahedral unfolding patches."""
from pathlib import Path
from math import sqrt
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

def embed(q):
    return (q[0]+q[1]/2, q[1]*sqrt(3)/2)

def edge(ax, u, v, color='#293a47', lw=1.2, style='-', z=2):
    (x0,y0),(x1,y1)=embed(u), embed(v)
    ax.plot([x0,x1],[y0,y1], linestyle=style, lw=lw, color=color, zorder=z)

def polygon(ax, corners, col):
    ax.add_patch(Polygon([embed(q) for q in corners], closed=True,
                         facecolor=col, edgecolor='#344b58', lw=1.0))

def label(ax, p, s, dx=0,dy=0):
    x,y=embed(p)
    ax.annotate(s,(x,y),xytext=(dx,dy),textcoords='offset points',ha='center',
                va='center',fontsize=10, color='#162630')

def point(ax,p,c):
    ax.plot(*embed(p),'o',ms=3.9,color=c,zorder=6)

fig,axes=plt.subplots(1,2,figsize=(7.0,2.95))
ax=axes[0]
u,v,w=(0,0),(2,0),(0,2)
b,c,d=(1,0),(0,1),(1,1)
h=(2/3,2/3)
for tri in ((u,b,c),(b,v,d),(c,d,w)):
    polygon(ax,tri,'#f6f8f9')
polygon(ax,(b,c,d),'#dbece8')
for mid in (b,c,d):
    edge(ax,mid,h,color='#527f80',lw=1.0,style='--')
edge(ax,u,h,color='#ac4f36',lw=2.2,z=4)
for q in (u,b,c,d,v,w):
    point(ax,q,'#364954')
point(ax,h,'#ac4f36')
for q,s,dx,dy in ((u,'$0$',-7,-5),(v,'$2e$',9,-4),(w,'$2f$',0,8),
                    (b,'$e$',0,-8),(c,'$f$',-8,1),(d,'$e+f$',14,2),
                    (h,'$h$',9,4)):
    label(ax,q,s,dx,dy)
ax=axes[1]
a,b,c=(0,0),(1,0),(0,1)
aa,bb,cc=(1,1),(0,2),(1,2)
for tri,col in zip(((a,b,c),(aa,b,c),(aa,bb,c),(aa,bb,cc)),
                   ('#dbece8','#f6f8f9','#f6f8f9','#e8e4ef')):
    polygon(ax,tri,col)
p,q=(.22,.31),(.64,1.8)
edge(ax,p,q,color='#ac4f36',lw=2.2,z=4)
for pos in (p,q):
    point(ax,pos,'#ac4f36')
for pos,s,dx,dy in ((a,'$A$',-4,-7),(b,'$B$',3,-7),(c,'$C$',-8,1),
                     (aa,r'$A^\prime$',9,0),(bb,r'$B^\prime$',-7,7),
                     (cc,r'$C^\prime$',6,7),(p,'$p$',9,0),(q,"$q'$",9,0)):
    label(ax,pos,s,dx,dy)
for ax,title in zip(axes,('Tetrahedron','Octahedron')):
    ax.set_title(title,loc='left',fontsize=11,fontweight='bold',color='#263b46',pad=0)
    ax.set_aspect('equal'); ax.set_xlim(-.2,2.25); ax.set_ylim(-.17,1.96)
    ax.axis('off')
fig.subplots_adjust(left=.025,right=.975,bottom=.02,top=.94,wspace=.15)
fig.savefig(Path(__file__).resolve().parents[1] / 'figures' / 'unfoldings.pdf',bbox_inches='tight',pad_inches=.025)
