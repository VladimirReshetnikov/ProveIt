#!/usr/bin/env python3
"""Regenerate the illustration and numerical examples for the report.

These are evaluations of proved formulas, not measurements of actual sets.
Requires Python 3, NumPy, and Matplotlib.
"""
from pathlib import Path
import json
import math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def guarantees(N, delta, eta, gamma):
    variance = delta * (1 - delta)
    angle = math.asin((1 - gamma) * eta / (2 * variance))
    length = max(1, math.floor(math.sqrt(N * angle / (2 * math.pi))))
    gain = delta * gamma * eta / (2 * delta - gamma * eta)
    return length, gain


def main():
    root = Path(__file__).resolve().parents[1]
    figures = root / 'figures'
    figures.mkdir(parents=True, exist_ok=True)
    N, delta, eta = 10**8, 0.1, 0.01
    gammas = np.linspace(0.01, 0.99, 800)
    pairs = [guarantees(N, delta, eta, float(g)) for g in gammas]
    fig, ax = plt.subplots(figsize=(7.0, 4.15), layout='constrained')
    ax.plot([x[0] for x in pairs], [x[1] / eta for x in pairs],
            color='#183B56', lw=2.4)
    for g in [0.25, 0.5, 0.75]:
        length, gain = guarantees(N, delta, eta, g)
        ax.scatter([length], [gain / eta], s=40, color='#087E8B', zorder=4)
        ax.annotate(r'$\gamma=' + str(g) + '$',
                    (length, gain / eta), xytext=(10, 7),
                    textcoords='offset points', fontsize=11, color='#183B56')
    ax.set_xlabel('Guaranteed minimum progression length', fontsize=11)
    ax.set_ylabel(r'Guaranteed density increment / $\eta$', fontsize=11)
    ax.set_title(r'$N=10^8,\quad \delta=0.1,\quad \eta=0.01$',
                 fontsize=12, color='#183B56', pad=12)
    ax.set_xlim(0, 1050)
    ax.set_ylim(0, 0.56)
    ax.grid(alpha=0.2, lw=0.7)
    ax.spines[['top', 'right']].set_visible(False)
    fig.savefig(figures / 'phase_frontier.pdf')
    fig.savefig(figures / 'phase_frontier.png', dpi=170)
    plt.close(fig)
    examples = []
    for delta, eta in [(0.5, 0.05), (0.1, 0.01), (0.01, 0.0001)]:
        length, gain = guarantees(N, delta, eta, 0.5)
        examples.append({
            'N': N, 'density': delta, 'normalized_correlation': eta,
            'gamma': 0.5,
            'baseline_continuous_length_bound': math.sqrt(eta*N/(128*math.pi)),
            'new_integer_length_bound': length,
            'baseline_density_increment': eta/4,
            'new_density_increment': gain,
        })
    payload = {'purpose': 'Illustration of theorem guarantees, not empirical data',
               'examples': examples}
    (root / 'formula_examples.json').write_text(json.dumps(payload, indent=2)+'\n')
    print(json.dumps(payload, indent=2))


if __name__ == '__main__':
    main()
