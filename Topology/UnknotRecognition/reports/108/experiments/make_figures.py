"""Exact combinatorial bound and measured parameter distribution figures."""
import argparse
from collections import Counter
import json
from math import factorial, log2
from pathlib import Path


def bell(n):
    row = [1]
    for _ in range(n):
        following = [row[-1]]
        for value in row:
            following.append(following[-1] + value)
        row = following
    return row[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = ap.parse_args()
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
        'axes.spines.top': False, 'axes.spines.right': False,
        'pdf.fonttype': 42, 'svg.fonttype': 'none'})
    saved = json.loads((args.root/'results/native_decisions_ordered.json').read_text())
    corpus = [c['finite_boundary']['parameters'] for c in saved['cases']
              if c['family'] == 'maintained_corpus']
    raw = Counter(p['raw_exceptional_columns'] for p in corpus)
    residual = Counter(p['exceptional_columns'] for p in corpus)
    factor = [{'k': k, 'ordered': 3**k * factorial(k) * bell(2*k),
               'distinguished': 3**k * bell(2*k+1)} for k in range(13)]
    fig, axes = plt.subplots(1, 2, figsize=(11.2, 3.8), layout='constrained')
    ks = range(11)
    axes[0].bar([k-.19 for k in ks], [raw[k] for k in ks], width=.38,
                label='Raw columns', color='#9eb7ca')
    axes[0].bar([k+.19 for k in ks], [residual[k] for k in ks], width=.38,
                label='After free closure', color='#234e70')
    axes[0].set(xlabel='Nonlinear columns k', ylabel='Number of cases',
                title='106 maintained finite-boundary inputs', xticks=list(ks))
    axes[0].legend(frameon=False, fontsize=9)
    axes[1].plot([r['k'] for r in factor], [log2(r['ordered']) for r in factor],
                 marker='o', markersize=3, label=r'$3^k k! B_{2k}$', color='#8094a3')
    axes[1].plot([r['k'] for r in factor], [log2(r['distinguished']) for r in factor],
                 marker='s', markersize=3, label=r'$3^k B_{2k+1}$', color='#234e70')
    axes[1].set(xlabel='Nonlinear columns k', ylabel='Log₂ enumeration bound',
                title='Worst-case combinatorial factors')
    axes[1].legend(frameon=False)
    figures = args.root/'article/figures'
    figures.mkdir(parents=True, exist_ok=True)
    for suffix in ('pdf', 'svg', 'png'):
        fig.savefig(figures/f'parameters_and_bounds.{suffix}', dpi=180)
    (args.root/'results/figure_data.json').write_text(json.dumps({
        'maintained_raw_k': dict(raw), 'maintained_residual_k': dict(residual),
        'bound_factors': factor,
        'scope': 'Left: recorded finite inputs; right: exact upper-bound factors, not timings.'},
        indent=2)+'\n')
    plt.close(fig)


if __name__ == '__main__':
    main()
