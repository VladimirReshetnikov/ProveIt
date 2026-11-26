#!/usr/bin/env python3
"""Exact checks for Kataoka, Table 7, rows lambda=5 and 7. Python 3 only."""
from collections import Counter
from math import comb

STEPS = {
    5: [(2, 2), (2, 1), (1, 2), (1, 0), (0, 1)],
    7: [(3, 3), (3, 2), (2, 3), (2, 1), (1, 2), (1, 1)],
}


def order_one_root(t, terms):
    """v_2 polynomial/root-sum value as (scaled order, e), returning None at zero."""
    m = 2 ** t
    e = max(1, m // 2)
    monomials = Counter()
    for exponent, c in terms.items():
        i = exponent % m
        monomials[i % e] += c if i < e else -c
    monomials = {i: c for i, c in monomials.items() if c}
    best = None
    for j in range(e):
        if best is not None and j >= best:
            break
        coefficient = sum(c * comb(i, j) for i, c in monomials.items() if i >= j)
        if coefficient:
            v2 = (abs(coefficient) & -abs(coefficient)).bit_length() - 1
            value = e * v2 + j
            best = value if best is None else min(best, value)
    return best, e


def symbol(steps):
    terms = Counter({(0, 0): 2 * len(steps)})
    for i, j in steps:
        terms[i, j] -= 1
        terms[-i, -j] -= 1
    return terms


def factor_check(lam, terms):
    # Multiplying the binomials by XOR implements arithmetic mod 2.
    factors = [(1, 0), (0, 1)] + [(1, 1)] * (lam - 2)
    terms_mod_two = {(i, j) for (i, j), c in terms.items() if c % 2}
    i0 = min(i for i, j in terms_mod_two)
    j0 = min(j for i, j in terms_mod_two)
    calculated = {(i0, j0)}
    for u, v in factors:
        calculated ^= {(i + u, j + v) for i, j in calculated}
    assert terms_mod_two == calculated


def shallow(lam, terms):
    from fractions import Fraction
    for branch in ('axis', 'diagonal'):
        max_order = 1 if branch == 'axis' else (lam - 2).bit_length()
        for t in range(max_order + 1):
            # Substitute (X,Y)=(W,Z) or (Z,W/Z), multiply by W^h Z^c.
            transformed = {(i, j) if branch == 'axis' else (j, i - j): value
                           for (i, j), value in terms.items()}
            h = -min(i for i, j in transformed)
            c = -min(j for i, j in transformed)
            degrees = max(j for i, j in transformed) + c
            weights = []
            for k in range(degrees + 1):
                coefficient = Counter()
                for (i, j), value in transformed.items():
                    if j + c >= k:
                        coefficient[i + h] += value * comb(j + c, k)
                value, e0 = order_one_root(t, coefficient)
                if value is not None:
                    weights.append((Fraction(value, e0), k))
            print('shallow', lam, branch, t, 'min=(v2,j)', min(weights))


def tree_values(lam, terms):
    tree_order = 0
    for s in range(1, 13):
        m = 2 ** s
        directions = [(a, 1) for a in range(m)] + [(1, b) for b in range(0, m, 2)]
        total = 0
        for a, b in directions:
            p = Counter()
            for (i, j), c in terms.items():
                p[a * i + b * j] += c
            total += order_one_root(s, p)[0]
        tree_order += total - 2
        prediction = ((5 * s + 5) * m - 16 * s + 22 if lam == 5
                      else (7 * s + 4) * m - 20 * s + 14)
        assert s < 3 or tree_order == prediction
        print('level', lam, s, 'shell', total, 'tree', tree_order)


if __name__ == '__main__':
    for lam, steps in STEPS.items():
        terms = symbol(steps)
        factor_check(lam, terms)
        shallow(lam, terms)
        tree_values(lam, terms)
