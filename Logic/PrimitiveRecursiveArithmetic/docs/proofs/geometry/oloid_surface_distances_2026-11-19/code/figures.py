"""Draw the folded chamber and a lifted two-crease path. Requires matplotlib/numpy."""
from pathlib import Path
import csv
import math
from fractions import Fraction
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from geometry import POINTS

ROOT = Path(__file__).resolve().parents[1]
T = 2 * math.pi / 3
r = math.sqrt(3)
marks = {(1,1):('o','#126567'), (1,-1):('^','#a94428'),
         (-1,1):('s','#355d8a'), (-1,-1):('D','#734a81')}

def planar(t):
    v = np.clip(np.tan(t/2)/r, 0, 1)
    w = np.sqrt((1-v)*(1+v))
    d = 1+3*v*v
    u = 2*r/9*(np.arcsin(v)+np.arctan2(2*v,w)+6*v*w/d)
    z = r/9*(np.log(d)+8*(1-1/d))
    a = np.stack((u,z),axis=-1)
    e = np.stack((-2*v*(1+v*v)*w/d, (1+v*v+2*v**4)/d),axis=-1)
    return a,a+r*e

def physical(t,s,ey,ez):
    c = np.cos(t)
    return np.stack(((1-s)*(-.5-c)+s*(.5-c/(1+c)),
        ey*(1-s)*np.sin(t),ez*s*np.sqrt(np.maximum(0,1+2*c))/(1+c)),axis=-1)

def folded(key):
    h,s,*_ = POINTS[key]
    a,b=planar(2*math.atan(float(h)))
    return a+float(s)*(b-a)

def inverted(p):
    lo,hi=0,T
    for _ in range(52):
        t=(lo+hi)/2
        a,b=planar(t)
        x,y=b-a
        if x*(p[1]-a[1])-y*(p[0]-a[0])<0:
            lo=t
        else:
            hi=t
    t=(lo+hi)/2
    a,b=planar(t)
    return t, np.dot(p-a,b-a)/3

def sheet(ax,light=False):
    ts=np.linspace(0,T,350)
    a,b=planar(ts)
    ax.add_patch(Polygon(np.r_[a,b[::-1]][:,::-1],fc='#f2f6f5',ec='none',zorder=0))
    for aa,bb in zip(*planar(np.linspace(0,T,15)[1:-1])):
        ax.plot([aa[1],bb[1]],[aa[0],bb[0]],color='#cad7d3',lw=.55)
    for points,co in [(a,'#277c6c'),(b,'#386a91'),
                      (np.array([a[0],b[0]]),'#849391'),(np.array([a[-1],b[-1]]),'#849391')]:
        ax.plot(points[:,1],points[:,0],color=co,lw=1.5)
    ax.set_aspect('equal')
    ax.set_xlim(-.18,3.35);ax.set_ylim(-.16,1.44)
    ax.axis('off')
    if not light:
        for x,y,ss,col in [(0.1,.64,'A','#277c6c'),(3.06,.47,'B','#386a91'),
                           (.75,-.08,'L','#697571'),(2.43,1.3,'R','#697571')]:
            ax.text(x,y,ss,color=col,ha='center',va='center',fontweight='bold',fontsize=9)

def constellation():
    fig,ax=plt.subplots(figsize=(7.2,2.9));sheet(ax)
    for key,(_,_,ey,ez) in POINTS.items():
        u,v=folded(key);m,col=marks[ey,ez]
        ax.scatter(v,u,s=33,marker=m,c=col,ec='white',lw=.7,zorder=5)
        delta={'P1':(-12,8),'P2':(7,0),'P3':(6,2),'P4':(7,-3),
               'P5':(-9,7),'P6':(6,-6),'P7':(6,3),'P8':(6,1),'P9':(-17,7),'P10':(1,7)}[key]
        ax.annotate(key,(v,u),xytext=delta,textcoords='offset points',fontsize=9,color=col)
    fig.savefig(ROOT/'figures/chamber.pdf',bbox_inches='tight',pad_inches=.01)
    plt.close(fig)

def example():
    with (ROOT/'data/distances.csv').open() as f:
        line=next(q for q in csv.DictReader(f) if q['from']=='P4' and q['to']=='P10')
    assert line['upper_route']=='AB'
    f,g=map(lambda v:float(Fraction(v)),line['upper_gate_parameters'].split())
    bmax=planar(T)[1]; a=planar(T*f)[0]; b=bmax-planar(T*g)[0]
    stops=[folded('P4'),a,b,folded('P10')]
    signs=[(1,-1),(1,1),(-1,1)]
    colors=['#b45131','#277c6c','#386a91']
    fig=plt.figure(figsize=(8,3.0))
    flat=fig.add_axes([.00,.12,.55,.77]);sheet(flat,light=True)
    body=fig.add_axes([.52,-.01,.49,1.01],projection='3d',computed_zorder=False)
    ts=np.linspace(0,T,110)
    for ey,ez in marks:
        for s in [0, .25,.5,.75,1]:
            xyz=physical(ts,s,ey,ez)
            body.plot(*xyz.T,color='#869a97' if s in (0,1) else '#cfd9d7',lw=.8 if s in (0,1) else .45)
        for tt in np.linspace(0,T,12):
            q=physical(np.full(2,tt),np.array([0,1]),ey,ez)
            body.plot(*q.T,color='#cbd5d3',lw=.5)
    for j,(p,q) in enumerate(zip(stops,stops[1:])):
        flat.plot([p[1],q[1]],[p[0],q[0]],color=colors[j],lw=2.3,solid_capstyle='round')
        pts=[]
        for frac in np.linspace(0,1,95):
            t,s=inverted(p*(1-frac)+q*frac)
            pts.append(physical(t,s,*signs[j]))
        pts=np.array(pts)
        body.plot(*pts.T,color=colors[j],lw=2.7,zorder=8)
        if j in (0,2):
            k=0 if j==0 else -1
            body.scatter(*pts[k],c=colors[j],s=18,zorder=12,edgecolors='white',linewidths=.5)
    for i,(p,k,offset) in enumerate(zip(stops,['P4','A','B','P10'],[(5,-1),(-17,6),(4,-14),(4,4)])):
        flat.scatter(p[1],p[0],s=19,zorder=5,ec='white',lw=.55,color='#263c42')
        flat.annotate(k,(p[1],p[0]),xytext=offset,textcoords='offset points',fontsize=9)
    body.set_box_aspect([3,2,2]);body.set(xlim=(-1.55,1.55),ylim=(-1,1),zlim=(-1,1))
    body.view_init(elev=17,azim=-69);body.set_axis_off()
    fig.savefig(ROOT/'figures/two_creases.pdf',bbox_inches='tight',pad_inches=.01)
    plt.close(fig)


def projections():
    fig, axes = plt.subplots(1,2, figsize=(8,2.55))
    outline_t = np.linspace(-T,T,240)
    xx = np.r_[-.5-np.cos(outline_t),1.5]
    yy = np.r_[np.sin(outline_t),0.]
    for j,(ax,axisname) in enumerate(zip(axes,('y','z'))):
        factor = 1 if j==0 else -1
        ax.fill(factor*xx,yy,color='#f3f6f5',edgecolor='#96a9a5',lw=.9)
        ax.axhline(0,color='#cdd8d5',lw=.6,zorder=0)
        for key,(h,s,ey,ez) in POINTS.items():
            coords = physical(2*math.atan(float(h)),float(s),ey,ez)
            m,col = marks[ey,ez]
            ax.scatter(coords[0],coords[j+1],marker=m,c=col,s=22,
                       edgecolors='white',linewidths=.5,zorder=4)
            offsets = {'P1':(-10,3), 'P2':(3,-8), 'P3':(3,4), 'P4':(-10,5),
                       'P5':(-5,4), 'P6':(-12,4), 'P7':(3,-7), 'P8':(-12,-5),
                       'P9':(-11,6), 'P10':(3,3)}
            ax.annotate(key[1:],(coords[0],coords[j+1]),xytext=offsets[key],
                        textcoords='offset points',color=col,fontsize=8)
        ax.set_aspect('equal')
        ax.set_xlim(-1.55,1.55);ax.set_ylim(-1.07,1.07)
        ax.set_xticks([-1,0,1]);ax.set_yticks([-1,0,1])
        ax.tick_params(length=2,pad=2,labelsize=7,colors='#58706c')
        for where in ('top','right'):
            ax.spines[where].set_visible(False)
        for where in ('bottom','left'):
            ax.spines[where].set(color='#b6c4c1',linewidth=.6)
        ax.set_xlabel('x',fontsize=9,labelpad=-7,loc='right')
        ax.set_ylabel(axisname,fontsize=9,rotation=0,labelpad=-5,loc='top')
    fig.subplots_adjust(wspace=.22,left=.045,bottom=.12,top=.97,right=.99)
    fig.savefig(ROOT/'figures/projections.pdf',bbox_inches='tight',pad_inches=.025)
    plt.close(fig)
if __name__ == '__main__':
    constellation()
    example()
    projections()
