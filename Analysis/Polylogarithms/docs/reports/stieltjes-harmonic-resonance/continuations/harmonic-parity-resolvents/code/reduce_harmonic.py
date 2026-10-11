#!/usr/bin/env python3
"""Exact nonpositive-index elimination for the relative harmonic interpolant.

Inputs are SymPy expressions.  A fixed nonpositive integer is eliminated;
symbols (and their integer shifts) remain free spectral indices.  This is a
finite exact algebra implementation, not a numerical continuation routine.
"""
from __future__ import annotations

from functools import lru_cache
import sympy as sp

A, B = sp.symbols('a b')


def clean(terms):
    return {w: sp.expand(c) for w, c in terms.items() if sp.expand(c) != 0}


def add(terms, word, coefficient):
    word = tuple(word)
    terms[word] = terms.get(word, sp.Integer(0)) + coefficient


def is_nonpositive(index):
    return index.is_Integer is True and index <= 0


def eliminate_one(word, position):
    """Apply the proved Bernoulli operator at one selected position."""
    word = tuple(map(sp.sympify, word))
    assert is_nonpositive(word[position])
    m = int(-word[position])
    q = m + 1
    terms = {}
    if len(word) == 1:
        return {(): (sp.bernoulli(q, A) - sp.bernoulli(q, B))/q}
    short = word[:position] + word[position+1:]
    if position == 0:
        add(terms, short, sp.bernoulli(q, A)/q)
    if position == len(word)-1:
        add(terms, short, -sp.bernoulli(q, B)/q)
    for k in range(q+1):
        factor = sp.binomial(q, k)/q
        if position > 0:
            target = list(short)
            target[position-1] -= k
            add(terms, target, factor*sp.bernoulli(q-k, 0))
        if position < len(word)-1:
            target = list(short)
            target[position] -= k
            add(terms, target, -factor*sp.bernoulli(q-k, 1))
    return clean(terms)


@lru_cache(maxsize=None)
def reduce_word(word, strategy='left'):
    """Return an exact dictionary {remaining word: endpoint polynomial}."""
    word = tuple(map(sp.sympify, word))
    positions = [i for i, s in enumerate(word) if is_nonpositive(s)]
    if not positions:
        return {word: sp.Integer(1)}
    if strategy == 'left':
        position = positions[0]
    elif strategy == 'right':
        position = positions[-1]
    elif strategy == 'middle':
        position = positions[len(positions)//2]
    else:
        raise ValueError(strategy)
    result = {}
    for shorter, factor in eliminate_one(word, position).items():
        for target, coefficient in reduce_word(shorter, strategy).items():
            add(result, target, factor*coefficient)
    return clean(result)


def negative_block(block, upper, lower):
    """The polynomial Pi_block(upper, lower)."""
    if not block:
        return sp.Integer(1)
    reduction = reduce_word(tuple(block))
    assert set(reduction) <= {()}
    return sp.expand(reduction.get((), 0).subs({A: upper, B: lower},
                                              simultaneous=True))


def gap_polynomial(word):
    """Canonical polynomial multiplying the surviving free summation indices."""
    word = tuple(map(sp.sympify, word))
    free = [s for s in word if not is_nonpositive(s)]
    if not free:
        return (), negative_block(word, A, B)
    y = sp.symbols('y1:'+str(len(free)+1))
    blocks = [[]]
    for s in word:
        if is_nonpositive(s):
            blocks[-1].append(s)
        else:
            blocks.append([])
    polynomial = negative_block(blocks[0], A, y[0]+1)
    for j in range(1, len(free)):
        polynomial *= negative_block(blocks[j], y[j-1], y[j]+1)
    polynomial *= negative_block(blocks[-1], y[-1], B)
    return y, sp.expand(polynomial)


def reduce_by_gaps(word):
    word = tuple(map(sp.sympify, word))
    free = tuple(s for s in word if not is_nonpositive(s))
    y, polynomial = gap_polynomial(word)
    if not free:
        return clean({(): polynomial})
    result = {}
    for powers, coefficient in sp.Poly(polynomial, *y).terms():
        add(result, tuple(s-n for s, n in zip(free, powers)), coefficient)
    return clean(result)


def finite_harmonic(word, b, count):
    """Independent strict nested finite sum by dynamic programming."""
    word = tuple(map(sp.sympify, word))
    if not word:
        return sp.Integer(1)
    values = [sp.Integer(0)]*len(word) + [sp.Integer(1)]
    for n in range(count):
        x = b+n
        # Left-to-right retains the previous smaller-index suffix values.
        for j in range(len(word)):
            values[j] += x**(-word[j])*values[j+1]
    return values[0]


def complete_harmonic(j, n):
    """[z^n] product_{ell=1}^j (1-z/ell)^(-1), an exact rational."""
    coefficients = [sp.Integer(1)] + [sp.Integer(0)]*n
    for ell in range(1, j+1):
        for r in range(1, n+1):
            coefficients[r] += coefficients[r-1]/ell
    return coefficients[n]


if __name__ == '__main__':
    s, t = sp.symbols('s t')
    for word in ((0, s, 0), (-1, s, -1), (s, 0, t),
                 (0, s, -1, t, 0), (-1, 0, s, 0, -2)):
        word = tuple(map(sp.sympify, word))
        print('WORD:', word)
        for target, coefficient in reduce_word(word).items():
            print(' ', target, ':', sp.factor(coefficient))
