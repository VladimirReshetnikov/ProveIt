"""Draw the sharp three-face route and the four-face flag certificate."""
from pathlib import Path
from cmath import exp, phase
from math import pi
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from dodeca_lower import FACES, basis_pentagon, adjacent_face
from dodeca_upper import coordinates

z = exp(2j*pi/5)

def to_plane(p):
    return sum(a*z**i for i,a in enumerate(p))

def develop(seq):
    ch = dict(zip(FACES[0],basis_pentagon))
    charts = [ch]
    for i,j in zip(seq,seq[1:]):
        ch = adjacent_face(i,j,ch)
        charts.append(ch)
    return [{k:to_plane(p) for k,p in ch.items()} for ch in charts]

def poly(ax, points, color, line='#43525a', width=1):
    ax.add_patch(Polygon([(p.real,p.imag) for p in points], closed=True,
                         facecolor=color, edgecolor=line, lw=width))

def marker(ax,p,label,dx,dy):
    ax.plot(p.real,p.imag,'o',ms=4,color='#983c28',zorder=6)
    ax.annotate(label,(p.real,p.imag),xytext=(dx,dy),textcoords='offset points',
                ha='center',va='center',fontsize=9.5,color='#232930',zorder=7)

def segment(ax,p,q,color,width,alpha=1):
    ax.plot([p.real,q.real],[p.imag,q.imag],color=color,lw=width,alpha=alpha)

def draw(ax,seq,lower):
    charts=develop(seq)
    s,t,hinges=coordinates(seq) if not lower else (None,None,None)
    p,q=charts[0][0],charts[-1][7]
    r=exp(-1j*phase(q-p))
    charts=[{i:(w-p)*r for i,w in face.items()} for face in charts]
    for j,(i,face) in enumerate(zip(seq,charts)):
        pts=[face[k] for k in FACES[i]]
        poly(ax,pts,['#eef4f1','#f4f5f5','#f3f4f5','#f2eff6'][j])
        c=sum(pts)/5
        if lower:
            off=.1-.23j if j==0 else -.05+.21j
            ax.text((c+off).real,(c+off).imag,str(i),ha='center',va='center',fontsize=8,color='#677782')
    if lower:
        P,Q=charts[0][0],charts[-1][7]
        segment(ax,P,Q,'#a34c34',2.5)
        marker(ax,P,'$V$',-5,8)
        marker(ax,Q,r'$-V$',9,6)
        phi=(5**.5+1)/2
        for k,x in enumerate([2-phi,(2+phi)/5],1):
            marker(ax,x*Q,'$t_{%d}$'%k,7,7)
    else:
        A=[(to_plane(pt)/10-p)*r for pt in s]
        B=[(to_plane(pt)/10-p)*r for pt in t]
        for a in A:
            for b in B: segment(ax,a,b,'#828e91',.75,.8)
        poly(ax,A,'#cee4de','#436d66',1.1)
        poly(ax,B,'#ded9eb','#6b5d8c',1.1)
        for a,b in zip([A[0],B[0]],['$V$',r'$-V$']):
            marker(ax,a,b,-8,6)
    ax.set_aspect('equal')
    ax.autoscale()
    ax.margins(x=.07,y=.12)
    ax.axis('off')

if __name__=='__main__':
    fig,axes=plt.subplots(1,2,figsize=(6.8,2.15))
    draw(axes[0],(0,3,10),True)
    draw(axes[1],(0,2,8,11),False)
    fig.subplots_adjust(left=.01,right=.99,bottom=.01,top=.99,wspace=.12)
    fig.savefig(Path(__file__).resolve().parent.parent/'figures'/'dodeca_strips.pdf',
                bbox_inches='tight',pad_inches=.025)
