#!/usr/bin/env python3
"""Create the report's mathematical illustrations (no generated imagery)."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_results import profile, remainder

ROOT=Path(__file__).resolve().parents[1]
FIG=ROOT/'figures'
FIG.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                    'axes.spines.top':False,'axes.spines.right':False,
                    'axes.titleweight':'bold','axes.labelcolor':'#273746',
                    'text.color':'#273746','axes.edgecolor':'#82909c'})

x=np.linspace(-5,5,801)
fig,ax=plt.subplots(1,2,figsize=(10.7,3.5),layout='constrained')
ax[0].plot(x,profile(0,x),color='#143d59',lw=2.5,label=r'$Q_0$ (Cauchy)')
for w,c in [(8,'#df8b39'),(20,'#309b99')]:
    ax[0].plot(x,profile(0,x)+profile(1,x)/w+profile(2,x)/w**2,
               color=c,lw=1.8,label=rf'$Q_0+Q_1/w+Q_2/w^2$, $w={w}$')
ax[0].set(xlabel='Rescaled displacement x',ylabel='Asymptotic profile',
          title='Universal small-time profile')
ax[0].legend(fontsize=8,frameon=False)
ax[1].plot(x,profile(1,x),color='#df8b39',lw=2,label=r'$Q_1(x)$')
ax[1].plot(x,profile(2,x),color='#309b99',lw=2,label=r'$Q_2(x)$')
ax[1].axhline(0,color='#a9b2b9',lw=.8)
ax[1].set(xlabel='Rescaled displacement x',ylabel='Correction coefficient',
          title='First two correction terms')
ax[1].legend(frameon=False,fontsize=9)
for a in ax:a.grid(alpha=.15)
fig.savefig(FIG/'universal_profiles.pdf',bbox_inches='tight')
fig.savefig(FIG/'universal_profiles.png',dpi=180,bbox_inches='tight')
plt.close(fig)

y=np.linspace(4,8,1001)
p=5
xx=y**p
rr=xx**(2/p)*remainder(xx,p)
fig,ax=plt.subplots(figsize=(9.5,3.8),layout='constrained')
ax.plot(y,rr,color='#143d59',lw=2.3,label=r'$x^{2/5}R(x)$, bounded positive-weight model')
ax.plot(y,.5*np.sin(np.pi*y)**2,color='#df8b39',ls='--',lw=1.3,
        label=r'Leading term $\frac{1}{2}\sin^2(\pi x^{1/5})$')
ax.scatter(np.arange(4,9),np.zeros(5),color='#a5363b',s=35,zorder=4,
           label=r'Samples $x=m^5$: exactly zero')
ax.set(xlabel=r'$x^{1/5}$',ylabel=r'$x^{2/5}R(x)$',ylim=(-.035,.57),
       title='A pole at s = 3/5 remains invisible at every fifth power')
ax.grid(alpha=.15)
ax.legend(fontsize=9,frameon=False,loc='upper center',
          bbox_to_anchor=(.5,-.20),ncol=1)
fig.savefig(FIG/'invisible_pole.pdf',bbox_inches='tight')
fig.savefig(FIG/'invisible_pole.png',dpi=180,bbox_inches='tight')
plt.close(fig)
print('Created universal_profiles and invisible_pole (PDF and PNG).')
