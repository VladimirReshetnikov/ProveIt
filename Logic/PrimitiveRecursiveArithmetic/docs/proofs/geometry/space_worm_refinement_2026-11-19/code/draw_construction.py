"""Reproduce a perspective view and an exact-coordinate section of the cover."""
import numpy as np
from matplotlib import pyplot as plt
from matplotlib.collections import PolyCollection
from matplotlib.collections import LineCollection
from scipy.spatial import ConvexHull
from scipy.optimize import brentq
from verify_spike import verts, H2, NORMALS, OFFSETS, Y

V=np.array(verts,float); H=np.sqrt(float(H2)); Y=float(Y)
E=np.array([0,H,H])
m=float(OFFSETS[3]/NORMALS[3][1])
scale=lambda z:np.sqrt(1-9*z*z)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,
                     'axes.spines.right':False,'axes.spines.top':False,
                     'pdf.fonttype':42})
fig,(ax,bx)=plt.subplots(1,2,figsize=(9.6,3.6),gridspec_kw={'width_ratios':[1.15,1]})
zz=np.linspace(0,H,90)
pts=np.vstack([np.c_[scale(z)*V,z*np.ones(4)] for z in zz]+[E])
hull=ConvexHull(pts)
target=np.array([.27,.18,.12]);viewer=np.array([1.5,2.2,2.1]);viewer/=np.linalg.norm(viewer)
right=np.cross([0.,0.,1.],viewer);right/=np.linalg.norm(right)
up=np.cross(viewer,right)
def uv(x): return np.atleast_2d(x)@np.array([right,up]).T
def show3(x,*args,**kw): ax.plot(*uv(x).T,*args,**kw)
ix=np.where(hull.equations[:,:3]@viewer>0)[0]
ix=ix[np.argsort((pts[hull.simplices[ix]].mean(axis=1)-target)@viewer)]
polys=[];colors=[]
for i in ix:
 tri=hull.simplices[i]; N=hull.equations[i,:3]
 warm=(len(pts)-1 in tri and N[2]<.99999)
 base=np.array([.94,.57,.26]) if warm else np.array([.74,.87,.85]) if N[2]>.99999 else np.array([.38,.71,.72])
 light=np.dot(N,np.array([.02,.42,.9]))
 colors.append(np.clip(base*(.82+.22*light)+.045,0,1))
 polys.append(uv(pts[tri]))
ax.add_collection(PolyCollection(polys,facecolors=colors,edgecolors=colors,linewidths=.25))
segments=[]
for i in ix:
 for opposite,j in enumerate(hull.neighbors[i]):
  if j>i and hull.equations[i,:3]@hull.equations[j,:3] < .91 and hull.equations[j,:3]@viewer>0:
   edge=np.delete(hull.simplices[i],opposite)
   segments.append(uv(pts[edge]))
ax.add_collection(LineCollection(segments,colors='#4d7779',linewidths=.72))
# Emphasize the outside silhouette, which is independent of tessellation.
p2=uv(pts);face=ConvexHull(p2);ids=list(face.vertices)+[face.vertices[0]]
ax.plot(*p2[ids].T,color='#244652',lw=1)
tag=uv(E)[0];ax.scatter(*tag,color='#8b3c16',s=20,zorder=20)
ax.annotate('Added point $E$',xy=tag,xytext=(13,13),textcoords='offset points',color='#7c3515',fontsize=9,
            arrowprops=dict(arrowstyle='-',color='#7c3515',lw=.7))
ax.set_aspect('equal');ax.autoscale();ax.margins(.12);ax.axis('off')
ax.set_title('The covering body',fontweight='semibold',pad=7)
z0=brentq(lambda z:H*scale(z)-m*(1-9*H*z),0,H)
line=lambda z:H+(m*scale(z0)-H)*(H-z)/(H-z0)
z=np.linspace(0,H,401);old=m*scale(z);new=np.where(z<z0,old,line(z))
bx.fill_betweenx(z,0,old,color='#c4ddda')
bx.fill_betweenx(z,old,new,color='#ed9a58')
bx.plot(old,z,color='#417276',lw=1.35)
bx.plot(new[z>=z0],z[z>=z0],color='#a55327',lw=1.65)
bx.plot(np.sqrt(1-z*z/Y**2)/3,z,color='#20445b',ls='--',lw=1.55,label='Turned prism vertex')
bx.scatter(H,H,s=24,color='#8b3c16',zorder=4)
bx.annotate('$E$',(H,H),xytext=(6,4),textcoords='offset points',color='#8b3c16')
bx.plot([0,H],[H,H],color='#417276',lw=1)
bx.set_xlim(0,.52);bx.set_ylim(0,.312)
bx.set_xlabel('$y$');bx.set_ylabel('$z$',rotation=0,labelpad=10)
bx.set_title('Section in the plane $x=0$',fontweight='semibold',pad=7)
bx.legend(frameon=False,loc='lower left',bbox_to_anchor=(.02,.04),fontsize=8)
bx.tick_params(color='#69858d',labelsize=8)
for s in ['left','bottom']:bx.spines[s].set_color('#69858d')
fig.tight_layout(pad=1.2,w_pad=2.1)
if __name__=='__main__':
    import sys
    out=sys.argv[1] if len(sys.argv)>1 else 'spike_figure.pdf'
    fig.savefig(out,bbox_inches='tight',pad_inches=.03)
