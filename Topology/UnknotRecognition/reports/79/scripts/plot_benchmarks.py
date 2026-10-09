#!/usr/bin/env python3
"""Render the article's static figure directly from retained benchmark data."""
import argparse
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--data', type=Path,
                    default=root/'repro/fast/shared_cover_research/results/summary.json')
parser.add_argument('--output', type=Path, default=root/'article/figures/benchmarks.pdf')
args = parser.parse_args()
data = json.loads(args.data.read_text())['records']
exhaustion = [r for r in data if r['experiment'] == 'exhaustion']
descent = [r for r in data if r['experiment'] == 'first_descent']
colors = ['#153D62', '#137C80']
plt.rcParams.update({'font.size': 9, 'axes.labelsize': 9,
                     'axes.titlesize': 10, 'legend.fontsize': 8,
                     'pdf.fonttype': 42, 'ps.fonttype': 42,
                     'axes.spines.top': False, 'axes.spines.right': False})
fig, axes = plt.subplots(1, 2, figsize=(7.2, 3.25), constrained_layout=True)
x = np.arange(len(exhaustion))
for offset, field, label, color in [(-.18, 'restart_frames', 'Restarted', colors[0]),
                                    (.18, 'shared_frames', 'Shared', colors[1])]:
    values = [r[field] for r in exhaustion]
    bars = axes[0].bar(x + offset, values, .34, label=label, color=color)
    axes[0].bar_label(bars, padding=3, fontsize=8)
axes[0].set_xticks(x, [str(r['tetrahedra']) for r in exhaustion])
axes[0].set_yscale('log')
axes[0].set_ylim(10, 9000)
axes[0].set_xlabel('Source tetrahedra')
axes[0].set_ylabel('Visited frames (log scale)')
axes[0].set_title('Complete covered-family search', loc='left', pad=10)
axes[0].legend(frameon=False, loc='upper left')
axes[0].grid(axis='y', alpha=.2, zorder=0)
axes[0].set_axisbelow(True)
sizes = [r['tetrahedra'] for r in descent]
for field, label, color, marker in [('restart_seconds', 'Restarted', colors[0], 'o'),
                                   ('shared_seconds', 'Shared', colors[1], 's')]:
    axes[1].plot(sizes, [r[field] for r in descent], color=color, marker=marker,
                 linewidth=1.5, markersize=4, label=label)
axes[1].set_xticks(sizes)
axes[1].set_yscale('log')
axes[1].set_ylim(.009, 30)
axes[1].set_xlabel('Source tetrahedra')
axes[1].set_ylabel('Median seconds (log scale)')
axes[1].set_title('First verified strict descent', loc='left', pad=10)
axes[1].legend(frameon=False, loc='lower right')
axes[1].grid(axis='y', alpha=.2)
args.output.parent.mkdir(parents=True, exist_ok=True)
fig.savefig(args.output)
fig.savefig(args.output.with_suffix('.png'), dpi=200)
print(args.output)
