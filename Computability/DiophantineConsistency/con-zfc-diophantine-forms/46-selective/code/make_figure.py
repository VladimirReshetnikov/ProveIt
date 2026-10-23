#!/usr/bin/env python3
"""Recreate the explanatory figure and target table (matplotlib required)."""
import collections
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
layout = json.loads((ROOT / 'data/layout.json').read_text())
data = json.loads((ROOT / 'data/raw_recipes.json').read_text())
w = layout['weights']
counts = collections.Counter(w[i] + w[j] for i in range(32) for j in range(i, 32))
protected = sorted({sum(a * b for a, b in zip(term['alpha'], w[1:]))
                    for row in data['rows'] for term in row})
if len(protected) != 62 or any(counts[e] != 1 for e in protected):
    raise ValueError('Invalid protected pair-sum data')

plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10})
fig, ax = plt.subplots(figsize=(9.1, 2.8), layout='constrained')
xs = sorted(counts)
ax.vlines(xs, 0, [counts[x] for x in xs], color='#a8b8c7', linewidth=1.1,
          label='All pair-sum multiplicities')
ax.scatter(protected, [1] * len(protected), s=12, color='#b74529', zorder=3,
           label='62 protected sums: multiplicity one')
ax.set(xlabel='Pair sum', ylabel='Multiplicity', xlim=(-4, 354), ylim=(0, max(counts.values()) + .5))
ax.set_yticks(range(0, max(counts.values()) + 1))
ax.spines[['top', 'right']].set_visible(False)
ax.grid(axis='y', color='#e7edf2', linewidth=.6)
ax.set_axisbelow(True)
ax.legend(frameon=False, loc='upper left', fontsize=9)
(ROOT / 'assets').mkdir(exist_ok=True)
fig.savefig(ROOT / 'assets/pair_sums.png', dpi=220)
plt.close(fig)

rows = []
for target, i in zip(layout['targets'], layout['row_permutation']):
    original = data['row_order_one_based'][i]
    sign = '-' if original in data['negated_original_rows'] else '+'
    rows.append((original, sign, target))
table = [r'\begin{table}[ht]', r'\centering',
         r'\begin{tabular}{rrr@{\qquad\qquad}rrr}', r'\toprule',
         r'Original row & Sign & Target & Original row & Sign & Target\\', r'\midrule']
for a, b in zip(rows[:11], rows[11:]):
    table.append(f'{a[0]} & ${a[1]}$ & {a[2]} & {b[0]} & ${b[1]}$ & {b[2]}' + r'\\')
table += [r'\bottomrule', r'\end{tabular}',
          r'\caption{Exact target assignment for the 22 original quadratic residuals.}',
          r'\label{tab:targets}', r'\end{table}']
(ROOT / 'target_table.tex').write_text('\n'.join(table) + '\n')
print('Created pair-sum figure and exact target table.')
