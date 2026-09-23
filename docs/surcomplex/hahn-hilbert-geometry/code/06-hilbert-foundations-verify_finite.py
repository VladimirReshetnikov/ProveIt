#!/usr/bin/env python3
"""Exact finite checks for Hilbert Geometry at Surreal Scales.

Python 3.10+, standard library only. These are checks of finite rational
identities, not proofs of the infinite-dimensional or proper-class theorems.
Run: python verify_finite.py --output verification.json
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import random
from typing import Sequence

Matrix = tuple[tuple[F, ...], ...]


def matrix(rows: Sequence[Sequence[int | F]]) -> Matrix:
    if not rows or not rows[0] or any(len(r) != len(rows[0]) for r in rows):
        raise ValueError("A matrix must be nonempty and rectangular.")
    return tuple(tuple(F(v) for v in row) for row in rows)


def shape(a: Matrix) -> tuple[int, int]:
    return len(a), len(a[0])


def identity(n: int) -> Matrix:
    return matrix([[int(i == j) for j in range(n)] for i in range(n)])


def transpose(a: Matrix) -> Matrix:
    return tuple(zip(*a))


def scale(c: F | int, a: Matrix) -> Matrix:
    return tuple(tuple(c * x for x in row) for row in a)


def add(a: Matrix, b: Matrix) -> Matrix:
    if shape(a) != shape(b):
        raise ValueError("Addition shape mismatch.")
    return tuple(tuple(x + y for x, y in zip(ar, br)) for ar, br in zip(a, b))


def subtract(a: Matrix, b: Matrix) -> Matrix:
    return add(a, scale(-1, b))


def multiply(a: Matrix, b: Matrix) -> Matrix:
    if len(a[0]) != len(b):
        raise ValueError("Multiplication shape mismatch.")
    bt = transpose(b)
    return tuple(tuple(sum((x * y for x, y in zip(row, col)), F(0))
                       for col in bt) for row in a)


def inverse(a: Matrix) -> Matrix:
    n, m = shape(a)
    if n != m:
        raise ValueError("Only square matrices are invertible here.")
    aug = [list(ar) + list(ir) for ar, ir in zip(a, identity(n))]
    for j in range(n):
        pivot = next((i for i in range(j, n) if aug[i][j]), None)
        if pivot is None:
            raise ValueError("Singular matrix.")
        aug[j], aug[pivot] = aug[pivot], aug[j]
        d = aug[j][j]
        aug[j] = [x / d for x in aug[j]]
        for i in range(n):
            if i != j:
                c = aug[i][j]
                aug[i] = [x - c * y for x, y in zip(aug[i], aug[j])]
    return tuple(tuple(row[n:]) for row in aug)


def graph_projector(b: Matrix) -> tuple[Matrix, Matrix]:
    """Return P=J (J^T J)^(-1) J^T and J=[I; B]."""
    _, n = shape(b)
    j = identity(n) + b
    gram = add(identity(n), multiply(transpose(b), b))
    p = multiply(multiply(j, inverse(gram)), transpose(j))
    return p, j


def verify() -> dict:
    counts: dict[str, int] = {}

    def check(group: str, label: str, actual: Matrix | list[F], expected: Matrix | list[F]) -> None:
        if actual != expected:
            raise AssertionError(f"Failed [{group}]: {label}")
        counts[group] = counts.get(group, 0) + 1

    # The two rank-one projectors and unnormalized intertwiner.
    for n in [1, 2, 3, 7, 31]:
        for tau in [F(1, 2), F(1, 13), F(-2, 5)]:
            q = n * tau
            p = scale(1 / (1 + q*q), matrix([[1, q], [q, q*q]]))
            r = subtract(identity(2), p)
            q0 = matrix([[1, 0], [0, 0]])
            d = subtract(p, q0)
            a = add(multiply(p, q0), multiply(r, subtract(identity(2), q0)))
            zero = matrix([[0, 0], [0, 0]])
            check('rank_one', 'P squared', multiply(p, p), p)
            check('rank_one', 'P symmetric', transpose(p), p)
            check('rank_one', 'R squared', multiply(r, r), r)
            check('rank_one', 'P R', multiply(p, r), zero)
            check('intertwiner', 'A Q = P A', multiply(a, q0), multiply(p, a))
            check('intertwiner', 'A^T A = I-D^2', multiply(transpose(a), a),
                  subtract(identity(2), multiply(d, d)))
            check('intertwiner', 'A A^T = I-D^2', multiply(a, transpose(a)),
                  subtract(identity(2), multiply(d, d)))
            check('intertwiner', 'D^2 commutes with P', multiply(multiply(d, d), p),
                  multiply(p, multiply(d, d)))

    # Rectangular and noncommuting matrix examples; no scalar commutation shortcuts.
    rng = random.Random(20260923)
    for m, n in [(1, 2), (2, 2), (3, 2), (2, 3)]:
        for _ in range(5):
            b = matrix([[F(rng.randint(-5, 5), rng.randint(1, 7))
                         for _ in range(n)] for _ in range(m)])
            p, j = graph_projector(b)
            check('graph', 'P squared', multiply(p, p), p)
            check('graph', 'P symmetric', transpose(p), p)
            check('graph', 'P J = J', multiply(p, j), j)
            q0 = matrix([[int(i == k and i < n) for k in range(n+m)]
                         for i in range(n+m)])
            a = add(multiply(p, q0),
                    multiply(subtract(identity(n+m), p), subtract(identity(n+m), q0)))
            d = subtract(p, q0)
            check('graph_intertwiner', 'A Q = P A', multiply(a, q0), multiply(p, a))
            check('graph_intertwiner', 'A^T A = I-D^2', multiply(transpose(a), a),
                  subtract(identity(n+m), multiply(d, d)))

    # Positive three-term block operator and finite graph kernel.
    for n in [1, 2, 4, 7]:
        tau = F(1, 11)
        s = matrix([[F(int(i == j), i+1) for j in range(n)] for i in range(n)])
        t = tuple(tuple(tau * int(i == j) for j in range(n)) +
                  tuple(-v for v in s[i]) for i in range(n))
        l = multiply(transpose(t), t)
        expected = tuple(tuple(tau*tau*int(i == j) for j in range(n)) +
                         tuple(-tau*v for v in s[i]) for i in range(n)) + \
                   tuple(tuple(-tau*v for v in s[i]) +
                         tuple(v for v in multiply(s, s)[i]) for i in range(n))
        check('positive_block', 'T^T T block formula', l, expected)
        d = matrix([[(i+1)*int(i == j) for j in range(n)] for i in range(n)])
        j = identity(n) + scale(tau, d)
        check('positive_block', 'T kills graph', multiply(t, j),
              matrix([[0]*n for _ in range(n)]))
        check('positive_block', 'L kills graph', multiply(l, j),
              matrix([[0]*n for _ in range(2*n)]))

    # Binomial square-root identities in Q[z]/(z^(N+1)).
    order = 14
    def coefficients(exponent: F) -> list[F]:
        cs = [F(1)]
        for k in range(1, order+1):
            cs.append(cs[-1] * (exponent - (k-1)) / k)
        return cs
    def convolution(a: list[F], b: list[F]) -> list[F]:
        return [sum((a[k] * b[j-k] for k in range(j+1)), F(0))
                for j in range(order+1)]
    root, invroot = coefficients(F(1, 2)), coefficients(F(-1, 2))
    check('formal_prefix', 'sqrt squared = 1+z', convolution(root, root),
          [F(1), F(1)] + [F(0)]*(order-1))
    check('formal_prefix', 'sqrt times inverse sqrt = 1', convolution(root, invroot),
          [F(1)] + [F(0)]*order)

    return {
        'status': 'PASS',
        'arithmetic': 'exact fractions.Fraction; no floating-point arithmetic',
        'checks_by_group': counts,
        'total_identity_checks': sum(counts.values()),
        'formal_prefix_order': order,
        'scope': 'Finite real rational matrix identities and formal polynomial prefixes only.',
        'not_verified_by_this_program': [
            'Infinite-dimensional unbounded-operator domain arguments',
            'Nonexistence of orthogonal meets or joins',
            'Baire category and automatic operator reconstruction',
            'Full Hahn support and arbitrary-rank convergence arguments',
            'Proper-class surreal or surcomplex assertions',
            'The theorems in a proof assistant',
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('verification.json'))
    args = parser.parse_args()
    result = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
