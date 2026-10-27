#!/usr/bin/env python3
"""Generate the report's table and scientific plot from recorded timings."""
import json
import os
from pathlib import Path
root = Path(__file__).resolve().parents[1]
d = json.loads((root/'results/benchmark_results.json').read_text())
rows = d['matched_modular']
out = [r'\begin{center}',r'\begin{tabular}{@{}rrrr@{}}',r'\toprule',
       r'$N$ & Direct modular (ms) & Incremental (ms) & Speedup\\',r'\midrule']
for row in rows:
    med = row['median_seconds']
    out.append(f"{row['dimension']} & {1000*med['matched_cubic']:.3f} & {1000*med['fast']:.3f} & {row['speedup']:.2f}\\\\")
out += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(root/'results/benchmark_table.tex').write_text('\n'.join(out)+'\n')
r = rows[-1]; h = d['historical_rational'][-1]
macros = {'matchedSpeedup':f"{r['speedup']:.2f}",
          'matchedSlowSeconds':f"{r['median_seconds']['matched_cubic']:.4f}",
          'matchedFastSeconds':f"{r['median_seconds']['fast']:.5f}",
          'historicalSpeedup':f"{h['speedup']:.2f}",
          'historicalSlowSeconds':f"{h['median_seconds']['historical']:.4f}",
          'historicalFastSeconds':f"{h['median_seconds']['fast']:.6f}"}
(root/'results/headline_values.tex').write_text('\n'.join('\\newcommand{\\'+k+'}{'+v+'}' for k,v in macros.items())+'\n')
# Matplotlib is optional; the already generated vector PDF is bundled.
os.environ.setdefault('MPLCONFIGDIR',str(root.parent/'mpl_cache'))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig, ax = plt.subplots(figsize=(6.7,3.7),layout='constrained')
xs=[x['dimension'] for x in rows]
for key,label,color in [('matched_cubic','Direct modular products','#98502e'),('fast','Incremental unit states','#166274')]:
    ys=[x['median_seconds'][key] for x in rows]
    ax.plot(xs,ys,marker='o',linewidth=1.9,color=color,label=label)
ax.set_xscale('log',base=2);ax.set_yscale('log')
ax.set_xticks(xs,labels=[str(x) for x in xs])
ax.set_xlabel('Table dimension N');ax.set_ylabel('Median seconds for both tables')
ax.grid(True,which='major',alpha=.18);ax.legend(frameon=False,loc='upper left')
ax.set_title('Complete Cauchy features modulo $2^{64}$',loc='left',pad=12)
fig.savefig(root/'figures/benchmark.pdf')
fig.savefig(root/'figures/benchmark.png',dpi=160)
print(json.dumps(macros,indent=2))
