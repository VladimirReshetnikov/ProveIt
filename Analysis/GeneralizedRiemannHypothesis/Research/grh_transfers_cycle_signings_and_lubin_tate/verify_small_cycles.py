#!/usr/bin/env python3
"""Exact unrestricted spectral classification for C_n(1,2), n=8,10,12,14.

Run with Python 3.8 or newer; only the standard library is used.
Every triangle sign word is checked. A short induced path in each cyclic window
provides a cheap necessary test before we check the two Hamilton holonomies.
"""
from fractions import Fraction
from itertools import product
from math import factorial

CASES = {8: Fraction(2327, 1000), 10: Fraction(2498, 1000),
         12: Fraction(2595, 1000), 14: Fraction(26551, 10000)}


def make_edges(word, holonomy):
    """For holonomy None use the open path; otherwise close the cycle."""
    n = len(word) + 2 if holonomy is None else len(word)
    if holonomy is None:
        edges = [(i, i+1, 1) for i in range(n-1)]
        edges.extend((i, i+2, t) for i, t in enumerate(word))
    else:
        a = [1] * (n-1) + [holonomy]
        edges = [(i, (i+1) % n, a[i]) for i in range(n)]
        edges.extend((i, (i+2) % n, t*a[i]*a[(i+1) % n]) for i, t in enumerate(word))
    return n, edges


def is_positive_definite(order, edges, diagonal, multiplier):
    """Sylvester's criterion using Bareiss integer elimination without swaps."""
    a = [[0]*order for _ in range(order)]
    for i in range(order):
        a[i][i] = diagonal
    for i, j, t in edges:
        a[i][j] = a[j][i] = multiplier * t
    previous = 1
    for k in range(order - 1):
        pivot = a[k][k]
        if pivot <= 0:
            return False
        for i in range(k+1, order):
            for j in range(i, order):
                numerator = pivot*a[i][j] - a[i][k]*a[k][j]
                value, remainder = divmod(numerator, previous)
                assert remainder == 0
                a[i][j] = a[j][i] = value
        previous = pivot
    return a[-1][-1] > 0


def below_cutoff(word, holonomy, cutoff):
    order, edges = make_edges(word, holonomy)
    return all(is_positive_definite(order, edges, cutoff.numerator, sign*cutoff.denominator)
               for sign in (1, -1))


def check_alternating_bound(n, cutoff):
    # G(n)^2 = 4+2 cos(2π/n)+2 cos(4π/n). Machin's formula and the alternating
    # arctangent series yield the lower bound for π. For the two arguments, cosine
    # is decreasing and its degree-8 Taylor polynomial bounds it from above.
    lower_pi = Fraction(333, 106)
    lower_atan = sum(Fraction((-1)**j, (2*j+1)*5**(2*j+1)) for j in range(4))
    assert lower_pi < 16*lower_atan - Fraction(4, 239)
    def upper_cos(x):
        return sum((-1)**j*x**(2*j)/factorial(2*j) for j in range(5))
    x = 2*lower_pi/n
    assert 4 + 2*upper_cos(x) + 2*upper_cos(2*x) < cutoff**2


def check_size(n, cutoff):
    check_alternating_bound(n, cutoff)
    length = n-4
    good = {w for w in product((1, -1), repeat=length) if below_cutoff(w, None, cutoff)}
    survivors = set()
    cycle_words = 0
    for w in product((1, -1), repeat=n):
        doubled = w + w
        if any(doubled[i:i+length] not in good for i in range(n)):
            continue
        cycle_words += 1
        for holonomy in (1, -1):
            if below_cutoff(w, holonomy, cutoff):
                survivors.add((w, holonomy))
    expected = {(tuple(s*(-1)**i for i in range(n)), -1) for s in (1, -1)}
    print(f'n={n}, cutoff={cutoff}, path words={len(good)}, cyclic words={cycle_words}, '
          f'classes below cutoff={len(survivors)}')
    if survivors != expected:
        print('Additional classes:', sorted(survivors - expected))
    assert survivors == expected


if __name__ == '__main__':
    for size, cutoff in CASES.items():
        check_size(size, cutoff)
    print('Only alternating triangle signs with negative holonomy survive at each size.')
