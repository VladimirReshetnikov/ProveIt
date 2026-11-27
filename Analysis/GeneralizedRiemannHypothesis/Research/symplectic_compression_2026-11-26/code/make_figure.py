#!/usr/bin/env python3
"""Render a publication figure from exact rational two-plane probabilities."""
from fractions import Fraction
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'axes.labelcolor':'#133247','text.color':'#133247',
                     'pdf.fonttype':42})
fig, ax = plt.subplots(1, 2, figsize=(10.2, 3.45), constrained_layout=True)
x=np.arange(2)
vals=[Fraction(11,720),Fraction(1,90)]
bars=ax[0].bar(x, [float(v) for v in vals], width=.57,
               color=['#007F86','#789CB3'])
ax[0].axhline(1/81,color='#BD6732',linestyle='--',linewidth=1.5,
              label='Uniform: 1/81')
ax[0].set_xticks(x,['det A = 1\n24 matrices','det A ≠ 1\n57 matrices'])
ax[0].set_ylabel('Probability of one matrix')
ax[0].set_title('Two symplectic planes over F₃\nAmbient dimension 4',loc='left',pad=12)
ax[0].set_ylim(0,.0193)
for bar, v in zip(bars,vals):
    ax[0].text(bar.get_x()+bar.get_width()/2,bar.get_height()+.00055,str(v),
               ha='center',fontweight='bold',fontsize=10)
ax[0].legend(frameon=False,loc='upper right',fontsize=9)
ns=list(range(1,9))
for q,c in [(2,'#007F86'),(3,'#789CB3'),(4,'#BD6732')]:
    values=[Fraction((q**3-q**2+1)*(q*q-1),q**3*(q**(2*n)-1)) for n in ns]
    ax[1].semilogy([2*n for n in ns],list(map(float,values)),'o-',
                   markersize=3.5,color=c,label=f'q = {q}')
ax[1].set_xlabel('Ambient dimension 2n')
ax[1].set_ylabel('Total variation distance')
ax[1].set_title('Exact approach to uniform entries\nFixed two-plane frames',loc='left',pad=12)
ax[1].set_xticks([2,4,6,8,10,12,14,16])
ax[1].grid(axis='y',which='major',alpha=.18)
ax[1].legend(frameon=False)
dest=ROOT/'figures'
dest.mkdir(exist_ok=True)
fig.savefig(dest/'two_plane_law.pdf')
fig.savefig(dest/'two_plane_law.png',dpi=180)
print('Saved exact two-plane figure.')
