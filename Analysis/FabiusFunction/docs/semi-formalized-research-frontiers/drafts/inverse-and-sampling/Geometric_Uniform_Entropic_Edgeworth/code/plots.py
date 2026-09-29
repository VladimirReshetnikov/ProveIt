#!/usr/bin/env python3
"""Regenerate the article's diagnostic figures from numerical_checks.csv."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
rows=list(csv.DictReader((ROOT/'data/numerical_checks.csv').open()))
eps=np.array([float(r['epsilon']) for r in rows])
order=np.argsort(eps)
eps=eps[order]
plt.rcParams['pdf.fonttype']=42
plt.rcParams['ps.fonttype']=42
(ROOT/'figures').mkdir(exist_ok=True)
fig,ax=plt.subplots(figsize=(6.7,3.65))
y=np.array([float(r['quartic_scaled_residual']) for r in rows])[order]
ax.plot(eps,y,'o',label='Fourier diagnostic')
x=np.linspace(0,.205,250)
d4=427297/4410000; d5=2612237/27562500
ax.plot(x,d4+d5*x,label=r'$d_4+d_5\epsilon$')
ax.axhline(d4,linestyle='--',label=r'$d_4=427297/4410000$')
ax.set_xlabel(r'$\epsilon=1-q$')
ax.set_ylabel(r'$(\Delta-d_2\epsilon^2-d_3\epsilon^3)/\epsilon^4$')
ax.legend(fontsize=9)
fig.tight_layout()
fig.savefig(ROOT/'figures/quartic_check.pdf')
fig.savefig(ROOT/'figures/quartic_check.png',dpi=160)
plt.close(fig)
fig,ax=plt.subplots(figsize=(6.7,3.65))
for n in [3,5,8]:
    residual=np.abs(np.array([float(r[f'residual_{n}']) for r in rows]))[order]
    mask=residual>1e-13
    ax.loglog(eps[mask],residual[mask],'o-',label=f'Truncation through order {n}')
ax.set_xlabel(r'$\epsilon=1-q$')
ax.set_ylabel('Absolute diagnostic residual')
ax.legend(fontsize=9)
fig.tight_layout()
fig.savefig(ROOT/'figures/truncation_errors.pdf')
fig.savefig(ROOT/'figures/truncation_errors.png',dpi=160)
plt.close(fig)
print('Wrote both figures.')
