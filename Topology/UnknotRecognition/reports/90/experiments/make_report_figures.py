"""Regenerate the report's static figure and routing table from retained results."""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
routing = json.loads((ROOT/'results/routing_benchmark.json').read_text())
search = json.loads((ROOT/'cancellation/artifacts/benchmark.json').read_text())
out = ROOT/'article/figures'
out.mkdir(exist_ok=True)
plt.rcParams.update({'font.size': 9, 'axes.titlesize': 10, 'axes.labelsize': 9,
                     'legend.fontsize': 8, 'pdf.fonttype': 42, 'ps.fonttype': 42,
                     'axes.spines.top': False, 'axes.spines.right': False})
fig, axes = plt.subplots(1, 2, figsize=(7.3, 3.45), constrained_layout=True)
colors = {'old': '#9A4D26', 'new': '#007F86'}
rows = search['complete_radius_two'][:4]
x = [r['tetrahedra'] for r in rows]
for key, label, color in [('all_supports','All supports',colors['old']),
                          ('clusters','Local profiles',colors['new'])]:
    values = [r['medians'][key] for r in rows]
    lower = [r['ranges'][key][0] for r in rows]
    upper = [r['ranges'][key][1] for r in rows]
    axes[0].plot(x, values, 'o-', color=color, label=label, lw=1.7, ms=4)
    axes[0].fill_between(x, lower, upper, color=color, alpha=.12)
axes[0].set(yscale='log', xlabel='Source tetrahedra', ylabel='Seconds',
            title='Complete two-edge candidate generation')
axes[0].set_xticks(x)
rows = routing['paired']
x = [r['copies'] for r in rows]
for key, samples, label, color in [
        ('explicit_median_seconds','explicit_samples','Explicit graph',colors['old']),
        ('routed_median_seconds','routed_samples','Routed kernel',colors['new'])]:
    axes[1].plot(x, [1000*r[key] for r in rows], 'o-', color=color,
                 label=label, lw=1.7, ms=4)
    axes[1].fill_between(x, [1000*min(r[samples]) for r in rows],
                        [1000*max(r[samples]) for r in rows], color=color, alpha=.12)
axes[1].set(xscale='log', yscale='log', xlabel='Original tile copies',
            ylabel='Milliseconds', title='Graph query and certificate replay')
for ax in axes:
    ax.grid(which='major', alpha=.16)
    ax.legend(frameon=False, loc='best')
fig.savefig(out/'performance.pdf')
fig.savefig(out/'performance.png', dpi=180)
plt.close(fig)
lines = [r'\begin{center}\small', r'\begin{tabular}{rrrrrr}',r'\toprule',
         r'Copies & Original edges & Kernel edges & Explicit (ms) & Routed (ms) & Paired ratio\\',
         r'\midrule']
for r in rows:
    lines.append(f"{r['copies']:,} & {r['original_edges']:,} & {r['kernel_edges']:,} & "
                 f"{1000*r['explicit_median_seconds']:.3f} & "
                 f"{1000*r['routed_median_seconds']:.3f} & {r['paired_ratio_median']:.2f}"+r'\\')
lines += [r'\bottomrule',r'\end{tabular}\end{center}']
(ROOT/'article/sections/routing_table.tex').write_text('\n'.join(lines)+'\n')
print('Regenerated performance PDF/PNG and the routing table.')
