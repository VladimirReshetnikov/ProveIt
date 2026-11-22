#!/usr/bin/env python3
"""Generate exact vector illustrations for the finite-topology chapter.

Requires matplotlib. No generated imagery, external image assets, or data
downloads are used. Output paths are relative to this archive's root.
"""
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'paper' / 'figures'


def draw_node(ax, xy, label, *, face='#eef2f7', edge='#364152'):
    ax.add_patch(Circle(xy, 0.049, facecolor=face, edgecolor=edge,
                        linewidth=1.6, zorder=3))
    ax.text(*xy, f'${label}$', ha='center', va='center',
            fontsize=15, color='#152335', zorder=4)


def draw_edge(ax, p, q, color='#6d7786'):
    ax.plot((p[0], q[0]), (p[1], q[1]), color=color,
            linewidth=1.7, solid_capstyle='round', zorder=1)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({
        'font.family': 'DejaVu Sans',
        'font.size': 11,
        'mathtext.fontset': 'dejavusans',
        'pdf.fonttype': 42,
        'ps.fonttype': 42,
        'savefig.facecolor': 'white',
    })
    fig, axes = plt.subplots(1, 2, figsize=(7.6, 4.5),
                             gridspec_kw={'wspace': 0.15})
    fig.subplots_adjust(left=0.025, right=0.975, top=0.88, bottom=0.06)
    fig.text(0.5, 0.975, 'Finite normality: a least point makes the difference',
             ha='center', va='top', fontsize=14, fontweight='bold',
             color='#152335')
    for ax in axes:
        ax.set_xlim(0, 1)
        ax.set_ylim(-0.33, 1.02)
        ax.set_aspect('equal')
        ax.axis('off')

    left, right = axes
    left.text(0.5, 0.99, 'NORMAL', ha='center', va='top',
              color='#166266', fontsize=12, fontweight='bold')
    left.text(0.5, 0.90, 'One least point in this component',
              ha='center', va='top', fontsize=9.6, color='#4e5968')
    lp = {'a': (0.50, 0.25), 'b': (0.22, 0.70), 'c': (0.78, 0.70)}
    draw_edge(left, lp['a'], lp['b'])
    draw_edge(left, lp['a'], lp['c'])
    draw_node(left, lp['a'], 'a', face='#d4efea', edge='#166266')
    draw_node(left, lp['b'], 'b')
    draw_node(left, lp['c'], 'c')
    left.text(0.5, 0.105, r'$a\preceq b,\qquad a\preceq c$',
              ha='center', va='top', fontsize=12)
    left.text(0.5, -0.035, 'Every nonempty closed set contains a.',
              ha='center', va='top', fontsize=10)
    left.text(0.5, -0.135, 'Disjoint closed sets can be separated.',
              ha='center', va='top', fontsize=10, color='#166266')

    right.text(0.5, 0.99, 'NOT NORMAL', ha='center', va='top',
               color='#9c481f', fontsize=12, fontweight='bold')
    right.text(0.5, 0.90, 'Two incomparable minimal points',
               ha='center', va='top', fontsize=9.6, color='#4e5968')
    rp = {'a': (0.22, 0.25), 'b': (0.78, 0.25), 'c': (0.50, 0.70)}
    draw_edge(right, rp['a'], rp['c'], color='#2369a1')
    draw_edge(right, rp['b'], rp['c'], color='#bb6429')
    draw_node(right, rp['a'], 'a', face='#dcecf9', edge='#2369a1')
    draw_node(right, rp['b'], 'b', face='#f9e8d8', edge='#bb6429')
    draw_node(right, rp['c'], 'c')
    right.text(0.22, 0.13, r'$A=\{a\}$', ha='center', va='top',
               color='#2369a1', fontsize=11)
    right.text(0.78, 0.13, r'$B=\{b\}$', ha='center', va='top',
               color='#9c481f', fontsize=11)
    right.text(0.5, -0.035, r'$\uparrow a\,\cap\,\uparrow b=\{c\}$',
               ha='center', va='top', fontsize=12)
    right.text(0.5, -0.135, 'Every pair of neighborhoods meets at c.',
               ha='center', va='top', fontsize=10, color='#9c481f')

    fig.text(0.5, 0.018, 'Hasse diagrams: upward means larger in the specialization order.',
             ha='center', va='bottom', fontsize=9, color='#4e5968')
    stem = OUT / 'finite_normality'
    fig.savefig(stem.with_suffix('.pdf'), bbox_inches='tight', pad_inches=0.12,
                metadata={'Title': 'Finite normality and Urysohn separation',
                          'Author': 'General Topology in iPRA research packet',
                          'Subject': 'Exact three-point Hasse diagrams'})
    fig.savefig(stem.with_suffix('.png'), dpi=200,
                bbox_inches='tight', pad_inches=0.12)
    plt.close(fig)
    print(stem.with_suffix('.pdf'))
    print(stem.with_suffix('.png'))


if __name__ == '__main__':
    main()
