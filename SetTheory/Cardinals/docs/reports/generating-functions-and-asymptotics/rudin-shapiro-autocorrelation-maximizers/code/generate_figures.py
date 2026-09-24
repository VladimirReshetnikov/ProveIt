#!/usr/bin/env python3
"""Optional figure reproduction; requires matplotlib. Data are certified separately."""
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]
rows=json.loads((ROOT/'data/certified_maxima.json').read_text())
figdir=ROOT/'figures';figdir.mkdir(exist_ok=True)
selected=[r for r in rows if r['m']<=80]
fig,ax=plt.subplots(figsize=(6.8,2.8))
ax.plot([r['m'] for r in selected],[r['delta'] for r in selected],marker='o',markersize=3,linewidth=0.9)
ax.set_yscale('symlog',linthresh=4)
ax.axvline(40,linestyle='--',linewidth=0.8)
ax.set_xlabel('Level m')
ax.set_ylabel(r'$k_m^* - \ell_m$ (symmetric-log scale)')
ax.set_title('The last departure from the nearest-integer location is at m = 39')
ax.grid(True,alpha=0.25)
fig.tight_layout()
fig.savefig(figdir/'maximizer_deviation.pdf')
fig.savefig(figdir/'maximizer_deviation.png',dpi=180)
plt.close(fig)

selected=[r for r in rows if r['m']<=100]
lam=1.658967081916994079346775156784
limit=0.382159525906012163546221394312
fig,ax=plt.subplots(figsize=(6.8,2.8))
ax.plot([r['m'] for r in selected],[r['value']/lam**r['m'] for r in selected],
        marker='o',markersize=2.8,linewidth=0.9,label=r'$A_m/\lambda^m$')
ax.axhline(limit,linestyle='--',linewidth=1,label='Proved limiting constant')
ax.set_xlabel('Level m')
ax.set_ylabel('Normalized peak sidelobe level')
ax.set_title('The peak has an exact cubic recurrence from m = 43 onward')
ax.grid(True,alpha=0.25)
ax.legend(fontsize=9)
fig.tight_layout()
fig.savefig(figdir/'peak_normalization.pdf')
fig.savefig(figdir/'peak_normalization.png',dpi=180)
plt.close(fig)
