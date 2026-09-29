#!/usr/bin/env python3
"""Plot recorded data without rerunning high-precision calculations."""
import json
from pathlib import Path
import matplotlib.pyplot as plt
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data'/'results.json').read_text())
rows=[r for r in data['direct_remainders'] if r['offset']==0]
x=[r['X'] for r in rows]
fig,ax=plt.subplots(figsize=(7.0,3.7))
ax.plot(x,[float(r['direct_ratio']) for r in rows],'o-',label='Direct inverse partial sum')
ax.plot(x,[float(r['forward_ratio']) for r in rows],'s--',label='Inverse of forward truncation')
ax.axhline(1,linestyle=':',label='Common leading prediction')
ax.set_xlabel(r'$X$, with $M=\lfloor\pi X\rfloor$')
ax.set_ylabel('Error divided by its signed leading scale')
ax.legend(fontsize=9)
ax.grid(True,alpha=.25)
fig.tight_layout()
fig.savefig(ROOT/'figures'/'direct_vs_forward.pdf')
fig.savefig(ROOT/'figures'/'direct_vs_forward.png',dpi=180)
plt.close(fig)
rows=data['densities']
fig,ax=plt.subplots(figsize=(7.0,3.7))
ax.plot([r['t'] for r in rows],[float(r['density_ratio']) for r in rows],'o-',label='Exact boundary density')
ax.plot([r['t'] for r in rows],[float(r['prediction_2']) for r in rows],'s--',label='Two-correction density expansion')
ax.set_xlabel(r'$t$')
ax.set_ylabel(r'$\rho(t)/(\pi t e^{-2\pi t})$')
ax.legend(fontsize=9)
ax.grid(True,alpha=.25)
fig.tight_layout()
fig.savefig(ROOT/'figures'/'spectral_density.pdf')
fig.savefig(ROOT/'figures'/'spectral_density.png',dpi=180)
plt.close(fig)
