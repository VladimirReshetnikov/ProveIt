"""Render the retained scheduler data; never generates replacement measurements."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT/'evidence/top_scheduler_benchmark.json').read_text())
cases = data['cases']
figure_dir = ROOT/'article/figures'
figure_dir.mkdir(exist_ok=True)
q = [c['interior_vertices'] for c in cases]

plt.rcParams.update({'font.size': 8, 'font.family': 'DejaVu Sans',
                     'axes.spines.top': False, 'axes.spines.right': False,
                     'axes.labelcolor': '#173349', 'text.color': '#173349',
                     'pdf.fonttype': 42, 'svg.fonttype': 'none'})
fig, axes = plt.subplots(1, 2, figsize=(6.5, 2.8), layout='constrained')
for ax, key, title in zip(axes, ('scheduler', 'source_incidence_plus_schedule'),
                          ('Scheduling only', 'Source incidence + scheduling')):
    for side, color, marker, label in (('left', '#ad6040', 'o', 'Repeated scan'),
                                       ('right', '#236b72', 's', 'Rooted queue')):
        y = [c[key][side]['median_ns']/1e6 for c in cases]
        low = [c[key][side]['q1_ns']/1e6 for c in cases]
        high = [c[key][side]['q3_ns']/1e6 for c in cases]
        ax.plot(q, y, color=color, marker=marker, linewidth=1.65,
                markersize=4.2, label=label)
        ax.fill_between(q, low, high, color=color, alpha=.12)
    ax.set_xscale('log', base=2)
    ax.set_yscale('log')
    ax.set_xticks(q, [str(n) for n in q])
    ax.set_xlabel('Interior source vertices q (t = 3q + 1)')
    ax.set_ylabel('Median time (ms; logarithmic scale)')
    ax.set_title(title, loc='left', weight='bold', pad=12)
    ax.grid(which='major', axis='y', color='#dde3e6', linewidth=.55)
    ax.legend(frameon=False, fontsize=7, loc='upper left')
fig.savefig(figure_dir/'local_scheduler.pdf')
fig.savefig(figure_dir/'local_scheduler.png', dpi=220)
plt.close(fig)

table = [r'\begin{tabular}{@{}rrrrrr@{}}', r'\toprule',
         r'$q$ & $t$ & Scan (ms) & Queue (ms) & Local ratio & Combined ratio\\',
         r'\midrule']
for c in cases:
    scheduler = c['scheduler']
    table.append(f"{c['interior_vertices']} & {c['tetrahedra']} & "
                 f"{scheduler['left']['median_ns']/1e6:.5f} & "
                 f"{scheduler['right']['median_ns']/1e6:.5f} & "
                 f"{scheduler['ratio_of_medians']:.2f}" + r'$\times$ & ' +
                 f"{c['source_incidence_plus_schedule']['ratio_of_medians']:.2f}" + r'$\times$\\')
table += [r'\bottomrule', r'\end{tabular}']
(ROOT/'article/scheduler_table.tex').write_text('\n'.join(table)+'\n')
print(json.dumps({'source': 'evidence/top_scheduler_benchmark.json',
                  'figures': ['article/figures/local_scheduler.pdf',
                              'article/figures/local_scheduler.png'],
                  'table': 'article/scheduler_table.tex'}))
