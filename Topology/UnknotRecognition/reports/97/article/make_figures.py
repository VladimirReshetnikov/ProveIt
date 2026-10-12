#!/usr/bin/env python3
"""Regenerate the article's scientific figure from the retained raw samples.

Requires matplotlib. The prebuilt vector PDF is included, so rebuilding the
article itself does not require Python plotting dependencies.
"""

from pathlib import Path
import json

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter, FixedLocator


def main():
    article = Path(__file__).resolve().parent
    data = json.loads((article.parent / 'artifacts/column_cancellation'
                       / 'column_cancellation_20261012.json').read_text())
    cases = data['synthetic_producer']
    rows = [r['rows'] for r in cases]
    colors = ['#18384e', '#00818a']
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                         'axes.spines.top': False, 'axes.spines.right': False,
                         'pdf.fonttype': 42, 'ps.fonttype': 42})
    fig, axes = plt.subplots(1, 2, figsize=(7.4, 3.05), layout='constrained')
    series = [
        ([r['before_median_seconds'] for r in cases],
         [r['after_median_seconds'] for r in cases], 'Median seconds per call'),
        ([r['before_stats']['entry_scans'] for r in cases],
         [r['after_stats']['incidence_visits'] for r in cases], 'Source operations'),
    ]
    for ax, (before, after, ylabel) in zip(axes, series):
        ax.loglog(rows, before, '-o', color=colors[0], label='Baseline', lw=1.6, ms=4)
        ax.loglog(rows, after, '-s', color=colors[1], label='Column peeling', lw=1.6, ms=4)
        ax.set_xlabel('Rows in the bidiagonal matrix')
        ax.set_ylabel(ylabel)
        ax.xaxis.set_major_locator(FixedLocator(rows))
        ax.xaxis.set_major_formatter(FuncFormatter(lambda x, _: f'{int(x):,}'))
        ax.tick_params(axis='x', which='minor', bottom=False)
        ax.grid(which='major', color='#dce3e6', linewidth=0.6)
        ax.legend(frameon=False, loc='upper left', fontsize=8)
    target = article / 'figures'
    target.mkdir(exist_ok=True)
    fig.savefig(target / 'cancellation_scaling.pdf', bbox_inches='tight')
    fig.savefig(target / 'cancellation_scaling.png', dpi=180, bbox_inches='tight')
    plt.close(fig)


if __name__ == '__main__':
    main()
