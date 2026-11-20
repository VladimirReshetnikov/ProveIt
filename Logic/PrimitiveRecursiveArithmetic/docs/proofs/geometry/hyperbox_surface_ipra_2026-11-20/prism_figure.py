"""Rebuild the exact-formula illustrations in the report."""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.ticker import MaxNLocator

plt.rcParams.update({"font.family":"DejaVu Sans","font.size":9,"axes.spines.top":False,
                     "axes.spines.right":False,"pdf.fonttype":42,"axes.edgecolor":"#546570"})
fig, (a,b) = plt.subplots(1,2,figsize=(8.1,3.05),layout='constrained',
                           gridspec_kw={'width_ratios':[1.05,1.15]})
T=5; d=3
x=np.linspace(0,1,300); M,m=np.meshgrid(x,x)
excess=m*m+(d-1)*M*M+np.minimum(2*T*m,2*T+2-2*(T+1)*M+2*m)
excess=np.ma.masked_where(m>M,excess)
palette=LinearSegmentedColormap.from_list('teal',['#edf6f1','#97cab3','#388777','#174f53'])
a.contourf(M,m,excess,levels=np.linspace(0,7.2,25),cmap=palette)
ct=a.contour(M,m,excess,levels=[1,3,5,6.5],colors='#f5faf6',linewidths=.7)
a.clabel(ct,fontsize=7,fmt='%g')
a.plot([0,1,1,0],[0,0,1,0],lw=1,color='#354d59')
a.plot([.6,1],[.6,0],color='#a24222',lw=1.5)
a.scatter([.6,1],[.6,1],c=['#d06030','#354d59'],s=27,zorder=5,clip_on=False)
a.annotate('maximum',(0.6,0.6),(.12,.72),arrowprops={'arrowstyle':'-', 'color':'#654a3b'},color='#8e3b20')
a.set(xlim=(-.02,1.03),ylim=(-.02,1.04),xlabel='Largest cap coordinate, M',ylabel='Smallest cap coordinate, m')
a.set_aspect('equal');a.set_title('Squared distance above 25',loc='left',fontweight='semibold',fontsize=10.5)
for N,col in [(3,'#9f592c'),(4,'#267d68'),(6,'#345b82')]:
    d=N-1
    T=np.linspace(1,5.4,400)
    gap=(T-1)*(4*T*T-3*d*T-d)/(4*T*T)
    b.plot(T,gap,color=col,label=f'N = {N}',lw=1.9)
    Tstar=(3*d+(9*d*d+16*d)**.5)/8
    b.plot(Tstar,0,'o',color=col,ms=4)
b.axhline(0,color='#637078',lw=.8,zorder=-1)
b.set(xlim=(1,5.4),xlabel='Prism length, C',ylabel='Interior candidate squared minus corner squared')
b.set_title('Where the farthest point changes',loc='left',fontweight='semibold',fontsize=10.5)
b.legend(loc='upper left',frameon=False,ncol=1,fontsize=8)
b.yaxis.set_major_locator(MaxNLocator(integer=True))
fig.savefig("prism_figure.pdf",bbox_inches='tight',pad_inches=.055)
