"""Illustrate the exactly solved fixed-source example; colors use sampled floating-point distances."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import ListedColormap
from fixed_exact import gram_matrix, strips

g = gram_matrix(['1','1','4','0','80/401','0'])
rows = strips(g, 2)
xy = np.linspace(0, 1, 281)
x, y = np.meshgrid(xy, xy)
candidates = []
for site, gates in rows:
    sx, sy = map(float, site)
    vx, vy = sx-x, sy-y
    low = np.zeros(x.shape)
    valid = np.ones(x.shape, bool)
    for p, q in gates:
        a, b = map(float, p)
        ex, ey = float(q[0]-p[0]), float(q[1]-p[1])
        cross = vx*ey-vy*ex
        with np.errstate(divide='ignore', invalid='ignore'):
            t = ((a-x)*ey-(b-y)*ex)/cross
            r = ((a-x)*vy-(b-y)*vx)/cross
        valid &= (t>=low-1e-10)&(t<=1+1e-10)&(r>=-1e-10)&(r<=1+1e-10)
        low = np.maximum(low,t)
    candidates.append(np.where(valid, vx*vx+vy*vy, np.inf))
arr = np.array(candidates)
d = np.sqrt(np.min(arr, axis=0))
d[~np.isfinite(d)] = np.nan
plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':9, 'axes.spines.top':False, 'axes.spines.right':False})
fig, (ax,bx) = plt.subplots(1,2,figsize=(7.0,3.1), layout='constrained')
pal = ['#c4ded7','#e9dbbc','#cbd9ed','#f6cfbb','#dcd1e3','#bfdbb2','#efdbce','#c5dee1','#e9d5b3','#bacadd']
ax.pcolormesh(xy,xy,np.argmin(arr,axis=0),shading='nearest',cmap=ListedColormap(pal),vmin=-.5,vmax=9.5,rasterized=True)
ax.contour(x,y,d,levels=[2.1,2.3,2.5,2.7,2.85],colors='#46665c',linewidths=.55)
X,Y=1281/1604,1247/1604
ax.plot([X],[Y],marker='*',markersize=13,c='#9c3925')
ax.annotate('farthest point',xy=(X,Y),xytext=(.15,.90),arrowprops={'arrowstyle':'->','color':'#303030'},fontsize=8)
ax.set(xlabel='first edge coordinate', ylabel='second edge coordinate',aspect='equal',xlim=(0,1),ylim=(0,1),title='Target face $u_3=1$')
bx.axhline(0,ls='--',lw=.8,color='#586872')
P=np.array([.2,1.05]);Q=np.array([1.75,-1.05]);R=np.array([.2,-1.05])
bx.plot(*zip(P,Q),color='#234740',lw=2)
bx.plot(*zip(P,R,Q),ls=':',color='#935533',lw=1.7)
bx.plot(*zip(P,Q),'o',color='#234740',ms=4)
bx.text(P[0]-.1,P[1]+.12,'$p$')
bx.text(Q[0]-.05,Q[1]-.20,'$h(p)$')
bx.text(1.73,.13,'glide axis',ha='right')
bx.text(.98,-1.23,'$g$',ha='center')
bx.text(-.05,.45,'$r$',ha='center')
bx.text(-.05,-.52,'$r$',ha='center')
bx.text(1.28,.58,'$|p-h(p)|^2$\n$=g^2+4r^2$',ha='center')
bx.set(xlim=(-.3,2.1),ylim=(-1.55,1.5),aspect='equal',title='An antipodal development')
bx.axis('off')
fig.savefig('surface_geometry.pdf',bbox_inches='tight')
