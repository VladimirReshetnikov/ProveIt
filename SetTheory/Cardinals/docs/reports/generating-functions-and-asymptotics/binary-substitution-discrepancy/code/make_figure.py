#!/usr/bin/env python3
"""Rebuild the manuscript figure. Requires Matplotlib; the verifier does not."""
import json
from pathlib import Path
import matplotlib.pyplot as plt


def main():
    root = Path(__file__).resolve().parent.parent
    rows = json.loads((root / 'data/finite_extrema.json').read_text())[:25]
    constant = (6 + 21**0.5) / 5
    fig, ax = plt.subplots(figsize=(8.2, 4.5))
    ax.plot([r['ones'] for r in rows],
            [float(r['max_error_one_decimal']) for r in rows],
            marker='o', markersize=4,
            label='Maximum error among 1-positions in the finite block')
    ax.axhline(2, linestyle='--', label='Conjectured upper bound: 2')
    ax.axhline(constant, linestyle=':',
               label=r'Sharp supremum: $(6+\sqrt{21})/5$')
    ax.set_xscale('log')
    ax.set_xlabel('Number of 1-positions checked')
    ax.set_ylabel(r'Maximum of $n(\sqrt{21}-1)/2-v(n)$')
    ax.set_title('A small discrepancy that exceeds 2 only at large indices')
    ax.grid(True, alpha=0.25)
    ax.legend(loc='lower right', fontsize=9)
    fig.tight_layout()
    output = root / 'figures'
    output.mkdir(exist_ok=True)
    fig.savefig(output / 'finite_maxima.pdf', bbox_inches='tight')
    fig.savefig(output / 'finite_maxima.png', dpi=180, bbox_inches='tight')
    plt.close(fig)


if __name__ == '__main__':
    main()
