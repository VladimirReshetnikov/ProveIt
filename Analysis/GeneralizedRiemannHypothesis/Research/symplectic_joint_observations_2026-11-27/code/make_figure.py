#!/usr/bin/env python3
"""Plot proven envelopes, not an estimate of the unknown exact TV curve."""
from pathlib import Path
from fractions import Fraction
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from exact_law import tv_bounds

ROOT = Path(__file__).resolve().parents[1]
(ROOT/'figures').mkdir(exist_ok=True)
(ROOT/'results').mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':10,
                     'axes.spines.top':False, 'axes.spines.right':False,
                     'pdf.fonttype':42, 'ps.fonttype':42})
q, n = 2, 30
ds = list(range(1,n+1))
rows=[]
for d in ds:
    triple=tv_bounds(q,n,(d,d,d))
    pair=tv_bounds(q,n,(d,d))
    rows.append({'d':d,'D':3*d,'triple_lower':triple['tv_lower'],
                 'triple_upper':triple['tv_upper'],'pair_upper':pair['tv_upper']})
with (ROOT/'results'/'certified_envelopes.csv').open('w',newline='') as out:
    writer=csv.DictWriter(out,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
lower=[float(Fraction(r['triple_lower'])) for r in rows]
upper=[float(Fraction(r['triple_upper'])) for r in rows]
pair=[float(Fraction(r['pair_upper'])) for r in rows]
fig,axes=plt.subplots(1,2,figsize=(10.4,3.8),layout='constrained')
ax=axes[0]
ax.fill_between(ds,lower,upper,color='#DCE8EF',label='Certified range for joint TV')
ax.plot(ds,upper,color='#13766D',lw=2,label='Upper bound')
ax.plot(ds,lower,color='#AF4A28',lw=2,label='Lower bound')
ax.axvline(20,ls=':',color='#44515D',lw=1)
ax.text(20.4,.47,'3d = 2n',fontsize=9,color='#44515D')
ax.set(xlim=(8,30),ylim=(-.02,1.04),xlabel='Vectors per frame d',ylabel='Total variation distance',
       title='Three frames in dimension 60 over F₂')
ax.legend(loc='upper left',fontsize=8,frameon=False)
ax=axes[1]
ax.semilogy(ds,pair,color='#13766D',lw=2,label='One block: TV upper bound')
deficit=[max(1-l,1e-16) for l in lower]
ax.semilogy(ds,deficit,color='#AF4A28',lw=2,label='Full triple: upper bound on 1 − TV')
ax.axvspan(21,27,color='#DCE8EF',alpha=.65)
ax.set(xlim=(15,29),ylim=(1e-9,2),xlabel='Vectors per frame d',ylabel='Certified error bound',
       title='Pairwise randomness and joint separation')
ax.legend(loc='lower left',fontsize=8,frameon=False)
fig.savefig(ROOT/'figures'/'dimension_threshold.pdf')
fig.savefig(ROOT/'figures'/'dimension_threshold.png',dpi=180)
print('Created certified threshold figure and exact rational data.')
