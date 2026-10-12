"""Render exact graph templates and recorded certificate sizes for the article.

This optional script requires matplotlib.  It does not rerun benchmarks and
does not fit or extrapolate an asymptotic curve from finite measurements.
"""

import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'article/figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                     'pdf.fonttype': 42, 'axes.spines.top': False,
                     'axes.spines.right': False})


def local_templates():
    points = {0: (-.9, -.65), 1: (.9, -.65), 2: (0, .92), 3: (0, -.12)}
    graphs = [
        (r'$C_3$', [(0, 1), (1, 2), (0, 2)], 0),
        (r'$C_4$', [(0, 1), (1, 3), (3, 2), (2, 0)], 0),
        (r'$K_4-e$', [(0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], 4),
        (r'$K_4$', [(i, j) for i in range(4) for j in range(i + 1, 4)], 8),
    ]
    fig, axes = plt.subplots(1, 4, figsize=(9.3, 2.7))
    for ax, (title, edges, index) in zip(axes, graphs):
        vertices = sorted({v for edge in edges for v in edge})
        for u, v in edges:
            ax.plot([points[u][0], points[v][0]], [points[u][1], points[v][1]],
                    color='#234c68', linewidth=2, zorder=1)
        for v in vertices:
            ax.scatter(*points[v], s=145, color='#dce9f0', edgecolor='#234c68',
                       linewidth=1.5, zorder=2)
        ax.set_title(title, fontsize=14, pad=8)
        ax.text(0, -1.13, f'Total end index: {index}', ha='center', fontsize=10)
        ax.set(xlim=(-1.15, 1.15), ylim=(-1.28, 1.08), aspect='equal')
        ax.axis('off')
    fig.subplots_adjust(left=.02, right=.98, top=.88, bottom=.02, wspace=.2)
    fig.savefig(OUT / 'local_characteristic_graphs.pdf', bbox_inches='tight')
    fig.savefig(OUT / 'local_characteristic_graphs.png', dpi=160, bbox_inches='tight')
    plt.close(fig)


def certificate_sizes():
    data = json.loads((ROOT / 'data/unused_handles_benchmark.json').read_text())
    rows = [r for r in data['records'] if r['id'].startswith('fibonacci_')]
    t = [r['tetrahedra'] for r in rows]
    fig, ax = plt.subplots(figsize=(6.7, 3.6))
    for arm, label, color, marker in [('native', 'Maintained certificate', '#626f7a', 'o'),
                                      ('new', 'Unused-component certificate', '#176989', 's')]:
        ax.plot(t, [r['certificate_bytes'][arm] / 1024 for r in rows],
                label=label, color=color, marker=marker, linewidth=1.8, markersize=5)
    ax.set_xscale('log', base=2)
    ax.set_yscale('log', base=2)
    ax.set_xlabel('Tetrahedra in the specified Fibonacci layered family')
    ax.set_ylabel('Compact JSON certificate size (KiB)')
    ax.set_xticks(t, [str(v) for v in t])
    ax.grid(True, which='major', color='#e1e6e9', linewidth=.65)
    ax.legend(frameon=False, loc='upper left', fontsize=9)
    fig.tight_layout()
    fig.savefig(OUT / 'certificate_sizes.pdf', bbox_inches='tight')
    fig.savefig(OUT / 'certificate_sizes.png', dpi=160, bbox_inches='tight')
    plt.close(fig)


if __name__ == '__main__':
    local_templates()
    certificate_sizes()
