#!/usr/bin/env python3
"""Plot a proved finite-data enclosure, not a simulated asymptotic curve.
Requires numpy and matplotlib. Run after verify.py.
"""
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt
from verify import ROOT, load_counts

counts = load_counts(ROOT / 'data' / 'counts.txt')
n = np.arange(100,201)
a = np.array([np.log(float(counts[int(i)])) for i in n])
x = np.linspace(100,200,2401)
A = np.interp(x,n,a)
t = np.log2(x/100)
lo = np.exp((A+np.log(2))/x)
hi = np.exp((A+np.log(21))/x)
fig, ax = plt.subplots(figsize=(7.2,3.75))
ax.fill_between(t,lo,hi,alpha=0.23,label='Proved enclosing band')
ax.plot(t,lo,linewidth=1.1,label='Lower bound')
ax.plot(t,hi,linewidth=1.1,linestyle='--',label='Upper bound')
ax.set_xlabel(r'Shifted phase $u=\log_2(x/100)$')
ax.set_ylabel(r'Growth base $\exp P(\log_2 100+u)$')
ax.set_xlim(0,1)
ax.legend(loc='upper right',fontsize=8)
ax.grid(True,alpha=0.25)
fig.tight_layout()
fig.savefig(ROOT/'figures'/'profile_enclosure.pdf')
fig.savefig(ROOT/'figures'/'profile_enclosure.png',dpi=160)
plt.close(fig)
print('Wrote figures/profile_enclosure.pdf and .png')
