#!/usr/bin/env python3
"""Regenerate the report's static figure from the two delivered source files.

Requires matplotlib; the machine verification scripts use only the standard
library and do not depend on this optional plotting script.
"""
from pathlib import Path
from collections import Counter
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
old = json.loads((ROOT / 'baseline/sites215.json').read_text())
new = json.loads((ROOT / 'machine/sites215r.json').read_text())
assert [r[1:] for r in old] == [r[1:] for r in new]
a = Counter(len(r[0]) for r in old)
b = Counter(len(r[0]) for r in new)
d = Counter(len(y[0])-len(x[0]) for x, y in zip(old, new))
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                     'axes.spines.top': False, 'axes.spines.right': False,
                     'pdf.fonttype': 42, 'ps.fonttype': 42})
fig, axes = plt.subplots(1, 2, figsize=(10.2, 3.5),
                         gridspec_kw={'width_ratios': [1.65, 1]})
xs = list(range(min(a.keys() | b.keys()), max(a.keys() | b.keys()) + 1))
axes[0].bar([x-.2 for x in xs], [a[x] for x in xs], .4,
            color='#9aa9ba', label='Primary K215')
axes[0].bar([x+.2 for x in xs], [b[x] for x in xs], .4,
            color='#126b76', label='K215-R41')
axes[0].set(xlabel='Instruction address length (bits)', ylabel='Primitive occurrences')
axes[0].legend(frameon=False, fontsize=9)
axes[0].set_title('Address-length distribution', loc='left', fontweight='bold')
keys = sorted(d)
axes[1].bar([str(x) for x in keys], [d[x] for x in keys],
            color=['#126b76' if x < 0 else '#9aa9ba' if x == 0 else '#b16b45' for x in keys])
axes[1].set(xlabel='New length minus old length (bits)', ylabel='Primitive occurrences')
axes[1].set_title('Changes at corresponding ordinals', loc='left', fontweight='bold')
for ax in axes:
    ax.set_axisbelow(True)
    ax.grid(axis='y', color='#e0e5e9', linewidth=.6)
fig.tight_layout(pad=1.2)
out = ROOT / 'figures'
out.mkdir(exist_ok=True)
fig.savefig(out / 'address_lengths.pdf', bbox_inches='tight')
fig.savefig(out / 'address_lengths.png', dpi=190, bbox_inches='tight')
print(json.dumps({'old_sum':sum(k*v for k,v in a.items()),
                  'new_sum':sum(k*v for k,v in b.items()),
                  'length_difference_counts':dict(sorted(d.items()))}, indent=2))
