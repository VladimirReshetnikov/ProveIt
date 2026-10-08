"""Regenerate the article's exact diagrams and scanner allocation profile.

Requires matplotlib.  The profile uses the saved PD and crossing order;
it makes one untimed complete scan and verifies its rank and peak against
the recorded benchmark before drawing anything.
"""
from __future__ import annotations
from collections import Counter
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'fast'))
from fastunknot.ordering import repeated_stages
from fastunknot.scan_fast import FastScan

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from matplotlib.ticker import StrMethodFormatter

NAVY, TEAL, RUST, LIGHT = '#17324D', '#087E8B', '#AD4D36', '#E1E6EB'
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                     'axes.spines.top': False, 'axes.spines.right': False,
                     'axes.labelcolor': NAVY, 'text.color': NAVY,
                     'pdf.fonttype': 42, 'savefig.facecolor': 'white'})
OUT = ROOT / 'paper' / 'figures'
OUT.mkdir(parents=True, exist_ok=True)


def allocation_profile():
    results = json.loads((ROOT / 'results/window_benchmark.json').read_text())
    case = next(c for c in results['cases'] if c['name'] == 'stress_braid5_36')
    pd = [tuple(c) for c in case['pd']]
    order = case['order']
    cache = len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
    scan = FastScan(shape_cache=cache)
    full = []
    for i, index in enumerate(order, 1):
        scan.add_crossing(pd[index], reduce_now=False)
        before = scan.live
        scan.eliminate()
        full.append({'processed': i, 'objects_before_elimination': before,
                     'objects_after_elimination': scan.live})
    assert scan.total_rank() == case['full_rank']
    assert max(r['objects_before_elimination'] for r in full) == case['full']['stats']['max_objects_before_elimination']
    actual = dict(Counter(h for m, h in zip(scan.mid, scan.deg) if m is not None))
    assert {str(k): v for k, v in actual.items()} == case['full']['by_degree']
    window = case['window']['stats']['window_profile']
    profile = {'case': case['name'], 'pd_sha256': case['pd_sha256'],
               'order': order, 'shape_cache': cache,
               'full': full, 'window': window,
               'scope': 'untimed full trace checked against saved benchmark; saved window trace'}
    (ROOT / 'results/allocation_profile.json').write_text(json.dumps(profile, indent=2) + '\n')
    return case, profile


def window_figure():
    case, profile = allocation_profile()
    n, a = case['crossings'], case['target_raw_degree']
    fig, (left, right) = plt.subplots(1, 2, figsize=(8.0, 3.6),
                                    gridspec_kw={'width_ratios': [1, 1.25]})
    background = [(i, h) for i in range(n + 1) for h in range(i + 1)]
    retained = [(i, h) for i, h in background if a - (n - i) - 1 <= h <= a + 1]
    left.scatter(*zip(*background), s=12, marker='s', c=LIGHT, linewidths=0)
    left.scatter(*zip(*retained), s=12, marker='s', c=TEAL, linewidths=0)
    left.scatter([n], [a], s=50, marker='s', c=RUST, edgecolors='white', linewidths=.6, zorder=5)
    left.plot([0, n], [a + 1, a + 1], color=TEAL, linewidth=.8)
    left.plot([n - a + 1, n], [0, a - 1], color=TEAL, linewidth=.8)
    left.annotate('Target and guards', xy=(36, 16), xytext=(14, 29),
                  arrowprops={'arrowstyle': '->', 'color': NAVY}, fontsize=9)
    left.set(xlim=(-1, 38), ylim=(-1, 38), xlabel='Processed crossings i',
             ylabel='Raw degree h', title='A. Retained support\na = b = 16')
    for key, color, label in [('full', RUST, 'Full scan'), ('window', TEAL, 'Exact H⁰ window')]:
        rows = profile[key]
        right.plot([r['processed'] for r in rows],
                   [r['objects_before_elimination'] for r in rows],
                   color=color, label=label, linewidth=2, marker='o', markersize=2.5)
    right.axhline(10000, color='#7F8791', linestyle='--', linewidth=1, label='10,000-object cap')
    right.text(35.7, 18050, '17,694', ha='right', va='bottom', color=RUST, fontsize=10)
    right.text(35.7, 8050, '7,692', ha='right', va='bottom', color=TEAL, fontsize=10)
    right.set(xlim=(1, 37), ylim=(0, 19500), xlabel='Processed crossings i',
              ylabel='Objects allocated before elimination',
              title='B. Measured allocation\n36-crossing input')
    right.yaxis.set_major_formatter(StrMethodFormatter('{x:,.0f}'))
    right.grid(axis='y', alpha=.18)
    right.legend(loc='upper left', frameon=False, fontsize=9)
    fig.tight_layout(pad=1.1, w_pad=2)
    for suffix in ('pdf', 'png'):
        fig.savefig(OUT / ('window_support_and_profile.' + suffix), dpi=170)
    plt.close(fig)


def triangle_figure():
    fig, axes = plt.subplots(1, 2, figsize=(7.8, 3.5))
    pos = {'a': (0, 0), 'b': (2, 0), 'c': (1, 1.732), 'd': (1, .577)}
    edges = [('a','b'), ('b','c'), ('c','a'), ('a','d'), ('b','d'), ('c','d')]
    for index, ax in enumerate(axes):
        points = dict(pos)
        current = list(edges)
        color = TEAL if index == 0 else RUST
        if index:
            points['e'] = (1, .19)
            current += [('a','e'), ('b','e'), ('d','e')]
        ax.add_patch(Polygon([points[x] for x in ('a', 'b', 'd')],
                              closed=True, facecolor=color, alpha=.10, edgecolor='none'))
        for u, v in current:
            ax.plot([points[u][0], points[v][0]], [points[u][1], points[v][1]],
                    color='#778896', linewidth=1.5, zorder=1)
        for u, v in [('a','b'), ('b','d'), ('d','a')]:
            ax.plot([points[u][0], points[v][0]], [points[u][1], points[v][1]],
                    color=color, linewidth=3, zorder=2)
        for name, (x, y) in points.items():
            ax.scatter([x], [y], c=NAVY, s=40, zorder=3)
            offsets = {'a': (-.10,-.10), 'b': (.10,-.10), 'c': (0,.12),
                       'd': (.11,.04), 'e': (0,-.10)}
            dx, dy = offsets[name]
            ax.text(x+dx, y+dy, name, ha='center', va='center', fontsize=11)
        ax.set_aspect('equal')
        ax.set(xlim=(-.35,2.35), ylim=(-.32,2.02))
        ax.axis('off')
        ax.set_title('Facial triangle in K₄' if index == 0 else 'Nonfacial triangle after insertion',
                     fontsize=11, pad=10)
        ax.text(1, -.31, 'One side is a single dual face' if index == 0 else 'Three dual faces on each side',
                ha='center', fontsize=9, color=color)
    fig.tight_layout(pad=.7, w_pad=2)
    for suffix in ('pdf', 'png'):
        fig.savefig(OUT / ('terminal_triangle.' + suffix), dpi=170,
                    bbox_inches='tight', pad_inches=.12)
    plt.close(fig)


if __name__ == '__main__':
    window_figure()
    triangle_figure()
    print('Regenerated exact figures and verified allocation_profile.json')
