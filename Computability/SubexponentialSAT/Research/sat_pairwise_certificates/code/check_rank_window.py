#!/usr/bin/env python3
"""Finite checks accompanying the rank-window proof, using exact arithmetic.

These checks do not prove the asymptotic theorem and do not implement SAT.
The proof is rank subadditivity and the modular determinant argument in the
report. Negative controls demonstrate why the precision premise is required.
"""
from fractions import Fraction
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def rank(matrix):
    a = [[Fraction(x) for x in row] for row in matrix]
    rows, cols = len(a), len(a[0])
    r = 0
    for col in range(cols):
        pivot = next((j for j in range(r, rows) if a[j][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        value = a[r][col]
        a[r] = [v / value for v in a[r]]
        for j in range(r + 1, rows):
            value = a[j][col]
            if value:
                a[j] = [v - value*w for v, w in zip(a[j], a[r])]
        r += 1
        if r == rows:
            break
    return r


def crossing(n, column=False):
    labels = [(a, b) for a in range(n) for b in range(n)]
    if column:
        return [[int(x == v and y == u) for y, v in labels]
                for x, u in labels]
    return [[int(x == v and y == u) for u, v in labels]
            for x, y in labels]


def checks():
    reconstructions = 0
    ranks = []
    for n in range(1, 5):
        c = crossing(n)
        require(rank(c) == n*n, 'row crossing rank')
        require(rank(crossing(n, column=True)) == n*n, 'column crossing rank')
        ranks.append({'alphabet_size': n, 'both_flattening_ranks': n*n})
        for valuation in range(3):
            for gap in (1, 2):
                p = valuation + gap
                d = (2**valuation) * 3
                for seed in range(2):
                    b = [[d*c[i][j] + 2**p*((17*i+11*j+7*seed) % 5 - 2)
                          for j in range(n*n)] for i in range(n*n)]
                    require(rank(b) == n*n, 'modular reconstruction lost full rank')
                    normalized = [[x // 2**valuation for x in row] for row in b]
                    require(all((normalized[i][j] - c[i][j]) % 2 == 0
                                for i in range(n*n) for j in range(n*n)),
                            'mod2 normalized matrix mismatch')
                    reconstructions += 1
    controls = []
    for n in (2, 3, 4):
        p = valuation = 3
        c = crossing(n)
        zero = [[0] * (n*n) for _ in range(n*n)]
        require(all((2**valuation*x) % 2**p == 0 for row in c for x in row),
                'insufficient precision control failed')
        require(rank(zero) == 0, 'zero matrix must have zero rank')
        controls.append({'alphabet_size': n, 'precision': p,
                         'scalar_valuation': valuation, 'allowed_lift_rank': 0})
    return {'status': 'PASS', 'crossing_ranks': ranks,
            'exact_modular_reconstructions': reconstructions,
            'insufficient_precision_negative_controls': controls,
            'scope': 'Finite illustrations; asymptotic proof is in report.tex.'}


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
