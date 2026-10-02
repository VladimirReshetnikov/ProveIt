#!/usr/bin/env python3
"""Create the two error-envelope figures used in the article."""
from __future__ import annotations
import math
from pathlib import Path
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]


def substitute(word: bytes, a: int, b: int) -> bytes:
    image1 = b"1" + b"0" * a + b"1" * b
    return b"".join(b"1" if c == 48 else image1 for c in word)


def prefix(a: int, b: int, n: int) -> bytes:
    word = b"1"
    while len(word) < n:
        word = substitute(word, a, b)
    return word[:n]


def errors(a: int, b: int, nletters: int):
    q = (math.sqrt((b + 1) ** 2 + 4 * a) - (b + 1)) / 2
    w = prefix(a, b, nletters)
    ranks = [0, 0]
    xs = {0: [], 1: []}
    ys = {0: [], 1: []}
    for pos, ch in enumerate(w, 1):
        letter = ch - 48
        ranks[letter] += 1
        n = ranks[letter]
        slope = 1 + q if letter == 1 else 1 + 1/q
        xs[letter].append(n)
        ys[letter].append(slope*n - pos)
    return xs, ys


def draw(a: int, b: int, title: str, bounds: dict[int, tuple[float,float]], outname: str):
    xs, ys = errors(a, b, 180_000)
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.plot(xs[1], ys[1], '.', markersize=0.7, alpha=0.45, label='positions of 1')
    ax.plot(xs[0], ys[0], '.', markersize=0.7, alpha=0.45, label='positions of 0')
    for letter in (0, 1):
        lo, hi = bounds[letter]
        ax.axhline(lo, linewidth=0.8, linestyle='--')
        ax.axhline(hi, linewidth=0.8, linestyle='--')
    ax.set_xscale('log')
    ax.set_xlabel('rank n (logarithmic scale)')
    ax.set_ylabel('linear position error')
    ax.set_title(title)
    ax.grid(True, linewidth=0.3, alpha=0.4)
    ax.legend(loc='best', markerscale=5)
    fig.tight_layout()
    fig.savefig(ROOT / 'figures' / f'{outname}.pdf', bbox_inches='tight')
    fig.savefig(ROOT / 'figures' / f'{outname}.png', dpi=180, bbox_inches='tight')
    plt.close(fig)


def main():
    r13 = math.sqrt(13)
    draw(
        1, 2,
        'A284368: errors remain inside much sharper envelopes',
        {1: ((r13-5)/3, (r13-2)/3), 0: ((1+r13)/3, (4+r13)/3)},
        'A284368_errors',
    )
    r3 = math.sqrt(3)
    draw(
        2, 1,
        'A284369: exact envelopes prove both OEIS position conjectures',
        {1: (-2, 1+r3), 0: (-(3+r3)/2, 2+r3)},
        'A284369_errors',
    )
    print('wrote figures')

if __name__ == '__main__':
    main()
