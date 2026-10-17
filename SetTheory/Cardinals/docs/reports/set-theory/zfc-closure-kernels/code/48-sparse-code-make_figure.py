#!/usr/bin/env python3
"""Regenerate the report's vector figure from its exact recorded proof family."""
from pathlib import Path
from math import isqrt
import json
import os
import tempfile
os.environ.setdefault('MPLCONFIGDIR',str(Path(tempfile.gettempdir())/'zfc-report-matplotlib'))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
records = json.loads((ROOT/'data/sparse_checker_tests.json').read_text())['balanced_truth_proofs']
x = [r['input_bits'] for r in records]
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'pdf.fonttype':42,'ps.fonttype':42})
fig, ax = plt.subplots(figsize=(6.7,3.65), layout='constrained')
grid = sorted(set([1,2,3,5,8,10,20,35,50,100,142,200,500,571,1000,2288,5000,9156,10000]))
ax.plot(grid,[isqrt(3*b+1) for b in grid],color='#737b86',linestyle='--',linewidth=1.5,
        label='All-input bound: floor sqrt(3b + 1)')
ax.plot(x,[r['unfolded_nodes']+1 for r in records],'-s',color='#be7132',markersize=4,
        label='Unfolded occurrences, plus zero row')
ax.plot(x,[r['sparse_rows'] for r in records],'-o',color='#164f7a',markersize=5,
        label='Canonical sparse rows')
ax.set_xscale('log'); ax.set_yscale('log')
ax.set_xlim(.85,12500); ax.set_ylim(.85,230)
ax.set_xlabel('Binary length of the proof code, b')
ax.set_ylabel('Rows / occurrences')
ax.set_xticks([1,10,100,1000,10000],['1','10','100','1,000','10,000'])
ax.set_yticks([1,2,5,10,20,50,100,200],['1','2','5','10','20','50','100','200'])
ax.grid(which='major',alpha=.2,linewidth=.6)
ax.legend(loc='upper left',fontsize=8.5,frameon=False)
ax.annotate('8 stored rows at 9,156 input bits',xy=(9156,8),xytext=(65,2.0),
            color='#164f7a',fontsize=9,
            arrowprops={'arrowstyle':'-','color':'#164f7a','linewidth':.8})
(ROOT/'figures').mkdir(exist_ok=True)
fig.savefig(ROOT/'figures/sparse_history.pdf',metadata={'Title':'Exact sparse history scaling','CreationDate':None})
plt.close(fig)
print('Wrote figures/sparse_history.pdf from the recorded exact integer data.')
