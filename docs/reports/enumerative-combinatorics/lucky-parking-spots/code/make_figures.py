#!/usr/bin/env python3
"""Optional figures, using matplotlib. Exact verification needs no dependencies."""
from __future__ import annotations
import csv
from pathlib import Path
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT/'figures'
OUT.mkdir(exist_ok=True)
rows = {}
with (ROOT/'data'/'triangle.csv').open(newline='',encoding='utf-8') as stream:
    for row in csv.DictReader(stream):
        n,j=int(row['n']),int(row['j'])
        rows.setdefault(n,[]).append((j,int(row['C_n_j'])/int(row['parking_functions'])))
fig,ax=plt.subplots(figsize=(7.2,3.7))
for n in (20,50,100):
    ax.plot([j/(n+1) for j,_ in rows[n]], [p for _,p in rows[n]],label=f'n = {n}')
ax.axhline(0.5, linestyle=':',linewidth=1)
ax.set(xlabel='Relative spot position j / (n + 1)',ylabel='Probability the spot is lucky',ylim=(0.34,1.025))
ax.legend(frameon=False)
ax.spines['top'].set_visible(False); ax.spines['right'].set_visible(False)
fig.tight_layout()
fig.savefig(OUT/'probability_profiles.pdf',bbox_inches='tight')
fig.savefig(OUT/'probability_profiles.png',dpi=170,bbox_inches='tight')
plt.close(fig)
limits=[]
with (ROOT/'data'/'boundary_limits.csv').open(newline='',encoding='utf-8') as stream:
    for row in csv.DictReader(stream):
        if int(row['j'])<=30: limits.append(row)
fig,ax=plt.subplots(figsize=(7.2,3.7))
x=[int(row['j']) for row in limits]
ax.plot(x,[float(row['rho_j']) for row in limits],marker='.',label='Left edge: spot j')
ax.plot(x,[float(row['beta_j_minus_1']) for row in limits],marker='.',label='Right edge: spot n − j + 1')
ax.axhline(0.5, linestyle=':',linewidth=1)
ax.set(xlabel='Edge index j (fixed before n tends to infinity)',ylabel='Limiting lucky-spot probability',ylim=(0.34,1.025))
ax.legend(frameon=False)
ax.spines['top'].set_visible(False); ax.spines['right'].set_visible(False)
fig.tight_layout()
fig.savefig(OUT/'boundary_limits.pdf',bbox_inches='tight')
fig.savefig(OUT/'boundary_limits.png',dpi=170,bbox_inches='tight')
plt.close(fig)
