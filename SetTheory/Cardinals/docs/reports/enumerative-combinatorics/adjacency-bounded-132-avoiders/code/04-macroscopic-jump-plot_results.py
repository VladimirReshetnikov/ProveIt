"""Rebuild the two article figures; requires NumPy and Matplotlib."""
from pathlib import Path
import csv
import numpy as np
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parents[1]
(root/'figures').mkdir(exist_ok=True)
x=np.linspace(.065,.62,800)
y=np.where(x<.5,3/np.sqrt(np.pi)*(1-2*x)/np.sqrt(x*(1-x)),0)
fig,ax=plt.subplots(figsize=(7.1,4.25))
ax.plot(x,y,label='Proved limiting profile',linewidth=1.7)
with (root/'data'/'simulation.csv').open() as file:
    rows=list(csv.DictReader(file))
for n in [1024,16384]:
    row=next(r for r in rows if int(r['n'])==n)
    cuts=[.1,.2,.3,.4,.55]
    vals=[float(row[f'scaled_tail_{u:g}']) for u in cuts]
    errs=[2*float(row[f'tail_standard_error_{u:g}']) for u in cuts]
    ax.errorbar(cuts,vals,yerr=errs,fmt='o',capsize=3,markersize=4,
                label=f'Uniform Catalan samples, n = {n:,}')
ax.axvline(.5,linestyle=':',linewidth=1)
ax.set(xlabel='Macroscopic deficit threshold u',
       ylabel=r'$\sqrt{n}\,\Pr(D_n>un)$',xlim=(.065,.62),ylim=(-.25,6.1))
ax.legend(frameon=False,fontsize=9)
fig.tight_layout()
fig.savefig(root/'figures'/'bulk_profile.pdf')
fig.savefig(root/'figures'/'bulk_profile.png',dpi=160)
plt.close(fig)

x=np.linspace(0,1,600)
y=np.sqrt(np.minimum(x,.5)/(1-np.minimum(x,.5)))
fig,ax=plt.subplots(figsize=(7.1,3.8))
ax.plot(x,y,linewidth=1.7,label='Limiting deficit-weighted CDF')
ax.plot([.2],[.5],'o',markersize=5)
ax.axvline(.5,linestyle=':',linewidth=1)
ax.annotate('Half the mean contribution lies above n/5',
            xy=(.2,.5),xytext=(.32,.27),
            arrowprops=dict(arrowstyle='->'),fontsize=9)
ax.set(xlabel='Deficit fraction x',ylabel='Fraction of the mean contributed below xn',
       xlim=(0,1),ylim=(0,1.05))
fig.tight_layout()
fig.savefig(root/'figures'/'mean_weighted_law.pdf')
fig.savefig(root/'figures'/'mean_weighted_law.png',dpi=160)
plt.close(fig)
