#!/usr/bin/env python3
"""Render the recorded kernel measurements; does not rerun timings."""
import json
import os
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
os.environ.setdefault('MPLCONFIGDIR', str(ROOT/'_build'/'mplconfig'))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

packing = json.loads((ROOT/'results/cached_balancing_benchmark.json').read_text())['results']
peeling = json.loads((ROOT/'results/precision_peeling_benchmark.json').read_text())['results']
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'pdf.fonttype':42,'savefig.bbox':'tight'})
fig, axes = plt.subplots(1,2,figsize=(9.2,3.3),constrained_layout=True)
x=[v['labels'] for v in packing]
axes[0].plot(x,[1000*v['baseline_median_seconds'] for v in packing],
             '-o',color='#667085',label='Existing exact code')
axes[0].plot(x,[1000*v['cached_median_seconds'] for v in packing],
             '-o',color='#176D9C',label='Cached row sums')
axes[0].set(yscale='log',xlabel='Label count Q',ylabel='Median time (ms)',
            title='Exact packet labeling',xticks=x)
axes[0].legend(frameon=False,loc='upper left',fontsize=8)
axes[0].grid(axis='y',alpha=.2)
removed=[100*v['V']/v['P'] for v in peeling]
ratios=[v['baseline_over_peeled'] for v in peeling]
axes[1].plot(removed,ratios,'-o',color='#176D9C')
axes[1].axhline(1,color='#667085',lw=.8,ls='--')
axes[1].set(xlabel='Guaranteed valuation removed (% of P)',
            ylabel='Full / peeled median time',title='Cyclic tensor arithmetic',
            ylim=(0,16),xticks=[0,25,50,75,100])
axes[1].grid(axis='y',alpha=.2)
fig.suptitle('Measured subroutine performance; no full SAT benchmark',fontsize=11)
out=ROOT/'figures';out.mkdir(exist_ok=True)
fig.savefig(out/'kernel_benchmarks.pdf')
fig.savefig(out/'kernel_benchmarks.png',dpi=180)
print('Rendered figures/kernel_benchmarks.pdf and .png')
