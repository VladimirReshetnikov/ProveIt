#!/usr/bin/env python3
"""Reproduce the three figures in article.tex with matplotlib defaults."""
from __future__ import annotations
import math
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
from verify import entry, catalan

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'figures'

def save(fig: plt.Figure, name: str) -> None:
    fig.tight_layout()
    fig.savefig(OUT / f'{name}.pdf')
    fig.savefig(OUT / f'{name}.png', dpi=180)
    plt.close(fig)

def main() -> None:
    OUT.mkdir(exist_ok=True)
    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    for n in (50, 200, 1000):
        total = (n + 2) * math.comb(2*n, n) - 4**n
        cumulative = 0
        values = [0.0]
        for k in range(1, n + 1):
            cumulative += entry(n, k) * 2**k
            values.append(cumulative / total)
        ax.plot(np.arange(n + 1) / n, values, label=f'Exact, n={n}')
    t = np.linspace(0, 1, 500)
    ax.plot(t, 1-np.sqrt(1-t), '--', linewidth=2, label='Limit: 1 − √(1 − t)')
    ax.set(xlabel='t', ylabel='Pr(Kₙ / n ≤ t), weighted by 2ᴷ',
           title='Critical weighting: a Beta(1, 1/2) limit')
    ax.legend(); ax.grid(alpha=0.25)
    save(fig, 'critical_cdf')

    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    for n in (100, 400, 1600):
        ks = np.arange(2, min(n, int(3.5*math.sqrt(n))) + 1)
        cn = catalan(n)
        ratios = [(entry(n,int(k))*2**(int(k)+3)) /
                  (cn*(int(k)-1)*(int(k)+4)) for k in ks]
        ax.plot(ks/math.sqrt(n), ratios, label=f'Exact, n={n}')
    s = np.linspace(0.001, 3.5, 500)
    ax.plot(s, 4*(-np.expm1(-s*s/4))/(s*s), '--', linewidth=2,
            label='Limit: 4(1 − exp(−s²/4)) / s²')
    ax.set(xlabel='s = k / √n', ylabel='Pr(Kₙ = k) / pₖ',
           title='The square-root crossover')
    ax.legend(); ax.grid(alpha=0.25)
    save(fig, 'crossover')

    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    ys = np.linspace(1.5, 2.5, 161)
    for n in (20, 60, 200):
        ks = np.array([k for k in range(1,n+1) if entry(n,k)>0])
        log_counts = np.array([math.log(entry(n,int(k))) for k in ks])
        means = []
        for y in ys:
            logs = log_counts + ks*np.log(y)
            weights = np.exp(logs-logs.max())
            means.append(float(np.dot(ks/n,weights)/weights.sum()))
        ax.plot(ys, means, label=f'Exact, n={n}')
    ax.axvline(2, linestyle=':', linewidth=1)
    ax.set(xlabel='Weight parameter y', ylabel='Weighted expectation of Kₙ / n',
           title='A sharp transition at y = 2')
    ax.legend(); ax.grid(alpha=0.25)
    save(fig, 'phase_transition')
    print('Saved three PDF/PNG figure pairs.')

if __name__ == '__main__':
    main()
