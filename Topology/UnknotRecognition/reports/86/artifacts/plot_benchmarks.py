"""Render the saved paired benchmark; no fits or extrapolations are used."""
from pathlib import Path
import csv
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
DATA = ROOT / 'edge_discovery' / 'benchmark.json'
benchmark = json.loads(DATA.read_text())['benchmark']
fixtures = {row['name']: row['tetrahedra'] for row in benchmark['fixtures']}
arms = [
    ('seeded_q_sector', 'Existing seeded Q-sector', '#48556a'),
    ('all_subspaces_k1', 'All weight spaces, k = 1', '#c77b31'),
    ('supplied_edge', 'Supplied edge 30', '#8a66a6'),
    ('global_one_edge', 'Global one-edge search', '#007f80'),
]
plt.rcParams.update({'font.size': 10, 'font.family': 'DejaVu Sans',
                     'axes.spines.top': False, 'axes.spines.right': False,
                     'pdf.fonttype': 42})
fig, ax = plt.subplots(figsize=(7.2, 4.3), layout='constrained')
csv_rows = []
for arm, label, color in arms:
    values = sorted((r for r in benchmark['summary'] if r['arm'] == arm),
                    key=lambda r: fixtures[r['fixture']])
    x = [fixtures[r['fixture']] for r in values]
    y = [r['median_seconds'] for r in values]
    low = [r['median_seconds'] - r['min_seconds'] for r in values]
    high = [r['max_seconds'] - r['median_seconds'] for r in values]
    ax.errorbar(x, y, yerr=[low, high], marker='o', markersize=4.5,
                linewidth=1.5, elinewidth=0.8, capsize=3, color=color,
                label=label, zorder=3)
    csv_rows.extend({'tetrahedra': fixtures[r['fixture']], 'method': arm,
                     'median_seconds': r['median_seconds'],
                     'min_seconds': r['min_seconds'],
                     'max_seconds': r['max_seconds']} for r in values)
ax.set_yscale('log')
ax.set_xticks([8, 16, 40, 72])
ax.set_xlim(4, 76)
ax.set_xlabel('Tetrahedra in the layered source')
ax.set_ylabel('Complete search time (seconds; logarithmic scale)')
ax.grid(axis='y', which='major', linewidth=0.6, color='#dbe0e6')
ax.legend(loc='upper left', frameon=False, fontsize=9)
fig.savefig(ROOT / 'benchmark_plot.pdf')
fig.savefig(ROOT / 'benchmark_plot.png', dpi=180)
with (ROOT / 'benchmark_summary.csv').open('w', newline='') as stream:
    writer = csv.DictWriter(stream, fieldnames=list(csv_rows[0]))
    writer.writeheader()
    writer.writerows(csv_rows)
print('Rendered benchmark plot and exact CSV summary.')
