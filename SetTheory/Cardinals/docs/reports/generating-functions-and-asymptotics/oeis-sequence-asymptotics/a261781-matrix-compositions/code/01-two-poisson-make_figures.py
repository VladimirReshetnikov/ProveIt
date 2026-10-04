#!/usr/bin/env python3
"""Regenerate the figure from verification results; requires matplotlib."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).resolve().parents[1]
rows=list(csv.DictReader((ROOT/'results/a261784_asymptotics.csv').open()))
fig,ax=plt.subplots(figsize=(6.6,3.8))
for j in range(4):
    ax.loglog([int(r['m']) for r in rows],
              [abs(float(r[f'relative_error_order_{j}'])) for r in rows],
              marker='o',markersize=4,label=f'{j} correction terms')
ax.set_xlabel('Index m in A261784')
ax.set_ylabel('Absolute relative error')
ax.grid(True,which='major',alpha=.25)
ax.legend(frameon=False,fontsize=9)
fig.tight_layout()
fig.savefig(ROOT/'figures/a261784_errors.pdf',bbox_inches='tight')
fig.savefig(ROOT/'figures/a261784_errors.png',dpi=160,bbox_inches='tight')
plt.close(fig)
