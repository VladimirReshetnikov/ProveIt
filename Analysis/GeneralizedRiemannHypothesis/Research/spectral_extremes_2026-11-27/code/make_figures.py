#!/usr/bin/env python3
"""Render scientific figures from the saved diagnostics (no new sampling)."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.special import erf

ROOT = Path(__file__).resolve().parents[1]
plt.rcParams.update({'font.size': 10, 'axes.titlesize': 11,
                     'axes.spines.top': False, 'axes.spines.right': False,
                     'pdf.fonttype': 42, 'figure.dpi': 150})
colors = ['#82a9c2', '#4987a8', '#1d5e80', '#133d55']


def finish(fig, name):
    fig.tight_layout(pad=1.6)
    fig.savefig(ROOT / 'figures' / (name + '.pdf'), bbox_inches='tight')
    fig.savefig(ROOT / 'figures' / (name + '.png'), dpi=180, bbox_inches='tight')
    plt.close(fig)


def main():
    (ROOT / 'figures').mkdir(exist_ok=True)
    data = json.loads((ROOT / 'results' / 'asymptotic_diagnostics.json').read_text())
    fig, axes = plt.subplots(1, 2, figsize=(10.0, 3.65))
    for c, curve in zip(colors, data['curves']):
        label = r'$u=10^{%d}$' % round(np.log10(curve['u']))
        axes[0].plot(curve['z'], curve['cdf'], color=c, lw=1.5, label=label)
        axes[1].plot(curve['y'], curve['exceedance_mark_cdf'], color=c, lw=1.5)
    z = np.linspace(-2.5, 5, 400)
    y = np.linspace(0, 3, 400)
    axes[0].plot(z, np.exp(-np.exp(-z)), '--', color='#c37d27', lw=2, label='Gumbel limit')
    axes[1].plot(y, erf(y), '--', color='#c37d27', lw=2, label=r'$\mathrm{erf}(y)$')
    axes[0].set(xlabel=r'Centered contribution $z$', ylabel='CDF',
                title='Maximum under the independent tilted law', xlim=(-2.5, 5), ylim=(0, 1.01))
    axes[1].set(xlabel=r'Rescaled height $y=\sqrt{b_u}\,\gamma/u$',
                ylabel='Fraction of exceedance intensity',
                title='Location marks at the exact threshold', xlim=(0, 3), ylim=(0, 1.01))
    axes[0].legend(frameon=False, fontsize=8, loc='lower right')
    axes[1].legend(frameon=False, fontsize=9, loc='lower right')
    finish(fig, 'tilted_extremes')

    simulations = json.loads((ROOT / 'results' / 'conditional_simulation.json').read_text())
    fig, axes = plt.subplots(1, 3, figsize=(10.4, 3.25))
    for color, sim in zip((colors[1], colors[3]), simulations):
        obs = np.asarray(sim['observations'])
        for k, ax in enumerate(axes):
            values = np.sort(obs[:, k])
            ax.plot(values, np.arange(1, len(values)+1)/len(values),
                    lw=1.5, color=color, label=f"u={sim['u']:g}, n={sim['n']}")
    grids = [np.linspace(-2, 6, 300), np.linspace(0, 2.5, 300), np.linspace(0, 5, 300)]
    limits = [np.exp(-np.exp(-grids[0])), erf(grids[1]), 1-np.exp(-grids[2])]
    labels = ['Centered maximum', 'Rescaled winning height', 'Boundary slack']
    xlims = [(-2, 6), (0, 2.5), (0, 5)]
    for ax, grid, lim, label, xlim in zip(axes, grids, limits, labels, xlims):
        ax.plot(grid, lim, '--', color='#c37d27', lw=1.8, label='Limiting law')
        ax.set(xlabel=label, ylabel='CDF', xlim=xlim, ylim=(0, 1.01))
    axes[0].legend(frameon=False, fontsize=8, loc='lower right')
    finish(fig, 'conditional_experiment')

    # Mathematical profile illustration: both are normalized limiting laws,
    # but the horizontal scales differ by sqrt(b).
    fig, axes = plt.subplots(1, 2, figsize=(10.0, 3.3))
    c = np.linspace(0, 6, 800)
    y = np.linspace(0, 3.5, 800)
    axes[0].plot(c, 2*np.arctan(c)/np.pi, color=colors[3], lw=2)
    axes[0].axvline(1, color='#c37d27', linestyle='--', lw=1.2)
    axes[0].set(xlabel=r'Height divided by the bulk scale: $c=\gamma/u$',
                ylabel='Cumulative fraction of total mass', title='Bulk: deterministic mass profile',
                xlim=(0, 6), ylim=(0, 1))
    axes[1].plot(y, 2/np.sqrt(np.pi)*np.exp(-y*y), color=colors[3], lw=2)
    axes[1].fill_between(y, 0, 2/np.sqrt(np.pi)*np.exp(-y*y), color=colors[0], alpha=.3)
    axes[1].set(xlabel=r'Height divided by the extreme scale: $y=\gamma/(u/\sqrt{b_u})$',
                ylabel='Probability density', title='Winner: random spectral location',
                xlim=(0, 3.5), ylim=(0, 1.2))
    finish(fig, 'two_scales')
    print('Rendered three vector-PDF figures and PNG previews.')


if __name__ == '__main__':
    main()
