"""Regenerate the article's static scientific figure from recorded samples."""

from pathlib import Path
import json
import statistics

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parents[2]
data = json.loads((ROOT / 'research/data/core_dual_paired_timings.json').read_text())
names = ['interior/mobius', 'interior/mobius_2', 'interior/mobius_8',
         'interior/mobius_64', 'interior/mobius_512']
by_name = {case['id']: case for case in data['cases']}
counts = [1, 2, 8, 64, 512]
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                     'axes.spines.top': False, 'axes.spines.right': False,
                     'pdf.fonttype': 42, 'ps.fonttype': 42})
fig, ax = plt.subplots(figsize=(7.1, 3.75), layout='constrained')
for method, label, color, marker in [
        ('max_weight', 'Compressed census + independent replay', '#167D8D', 'o'),
        ('explicit', 'Regina explicit cut + recognition', '#B85A26', 's')]:
    samples = [[1000 * (sample[method] if method == 'explicit'
                       else sample[method]['total'])
                for sample in by_name[name]['samples']] for name in names]
    mid = [statistics.median(values) for values in samples]
    lower = [m - min(values) for m, values in zip(mid, samples)]
    upper = [max(values) - m for m, values in zip(mid, samples)]
    ax.errorbar(counts, mid, yerr=[lower, upper], label=label, color=color,
                marker=marker, markersize=5.5, linewidth=1.8,
                capsize=3, elinewidth=1, zorder=3)
ax.set_xscale('log', base=2)
ax.set_yscale('log')
ax.set_xticks(counts, ['1', '2', '8', '64', '512'])
ax.set_yticks([1, 3, 10, 30, 100], ['1', '3', '10', '30', '100'])
ax.set_xlabel('Multiplicity of a fixed four-tetrahedron Möbius surface')
ax.set_ylabel('Whole-query time (milliseconds)')
ax.grid(True, which='major', color='#D7DEE4', linewidth=0.7, zorder=0)
ax.legend(frameon=False, loc='upper left', fontsize=8.7)
ax.set_ylim(0.7, 120)
destination = ROOT / 'article/figures'
destination.mkdir(parents=True, exist_ok=True)
fig.savefig(destination / 'mobius_capacity.pdf', metadata={
    'Title': 'Measured whole-cut query time on one source family',
    'Author': 'ProveIt research contribution'})
fig.savefig(destination / 'mobius_capacity.png', dpi=220)
plt.close(fig)
print('Wrote article/figures/mobius_capacity.pdf and .png')
