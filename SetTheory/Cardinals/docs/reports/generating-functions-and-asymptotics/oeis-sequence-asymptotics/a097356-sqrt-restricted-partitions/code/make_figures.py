"""Recreate the report's figures from saved verification data.

Usage: python make_figures.py --data results/plot_data.json --output figures
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import matplotlib.pyplot as plt
import numpy as np


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=Path('results/plot_data.json'))
    parser.add_argument('--output', type=Path, default=Path('figures'))
    args = parser.parse_args()
    if not args.data.is_file():
        parser.error(f'input data does not exist: {args.data}')
    data = json.loads(args.data.read_text(encoding='utf-8'))
    block = data['block']
    if not block:
        parser.error('plot data contains an empty block')
    m = (len(block)-1)//2
    args.output.mkdir(parents=True, exist_ok=True)
    theta = [row['theta'] for row in block]
    fig, ax = plt.subplots(figsize=(8, 4.6))
    ax.plot(theta, [row['normalized'] for row in block],
            label='Exact partition counts', linewidth=2)
    ax.plot(theta, [row['leading'] for row in block],
            '--', label='Leading phase factor')
    ax.plot(theta, [row['first'] for row in block],
            ':', label='First corrected expansion', linewidth=2)
    ax.set_xlabel(r'Phase $\theta=\{\sqrt{N}\}$')
    ax.set_ylabel(r'$N\,A(N)e^{-H\sqrt{N}}/C$')
    ax.set_title(f'A097356 within the square block m = {m}')
    ax.legend()
    ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(args.output/'phase_profile.pdf')
    fig.savefig(args.output/'phase_profile.png', dpi=160)
    plt.close(fig)

    eta = np.linspace(0, 1, 501)
    gamma = float(data['gamma'])
    if not 0 < gamma < 1:
        parser.error('gamma must lie strictly between zero and one')
    psi = np.minimum(eta/gamma, 1)-eta
    fig, ax = plt.subplots(figsize=(8, 4.3))
    ax.plot(eta, psi, linewidth=2)
    ax.axvline(gamma, linestyle='--', label=fr'$\gamma={gamma:.6f}$')
    ax.set_xlabel(r'Inverse phase $\eta=\{X(Y)\}$')
    ax.set_ylabel(r'$T(X)-X$')
    ax.set_title('The correction missed by a phase-blind inverse')
    ax.legend()
    ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(args.output/'inverse_phase.pdf')
    fig.savefig(args.output/'inverse_phase.png', dpi=160)
    plt.close(fig)


if __name__ == '__main__':
    main()
