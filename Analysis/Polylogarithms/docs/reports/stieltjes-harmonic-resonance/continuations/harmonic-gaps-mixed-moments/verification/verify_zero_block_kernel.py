#!/usr/bin/env python3
"""Exact independent checks for the all-depth relative geometric kernel.

No floating-point arithmetic or external packages are used.  Exponential
nodes are positive fourth powers, so quarter-integral endpoints give exact
rational values even when the interval length is not an integer.
These checks corroborate finite algebra; analytic proofs are in the paper.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
import json
import sys


def kernel(a4, b4, roots):
    """a=a4/4, b=b4/4 and exp(-x_j)=roots[j]**4."""
    if not roots:
        return F(1)
    cumulative = [F(1)]
    for root in roots:
        cumulative.append(cumulative[-1] * root)
    nodes = [root**4 for root in cumulative]
    dd = F(0)
    for j, root in enumerate(cumulative):
        denominator = F(1)
        for ell, node in enumerate(nodes):
            if ell != j:
                denominator *= nodes[j] - node
        dd += root ** (a4 - b4) / denominator
    prefactor = cumulative[-1] ** b4
    for node in nodes[1:-1]:
        prefactor *= node
    return prefactor * dd


def infinite_kernel(c4, roots):
    if not roots:
        return F(1)
    cumulative = F(1)
    denominator = F(1)
    prefactor = F(1)
    for j, root in enumerate(roots):
        cumulative *= root
        node = cumulative**4
        denominator *= 1 - node
        if j < len(roots) - 1:
            prefactor *= node
    return cumulative**c4 * prefactor / denominator


def finite_kernel(b4, length, roots):
    out = F(0)
    for increasing in combinations(range(length), len(roots)):
        out += product_fraction(
            root ** (4*n + b4)
            for root, n in zip(roots, reversed(increasing))
        )
    return out


def product_fraction(values):
    answer = F(1)
    for value in values:
        answer *= value
    return answer


def binomial(x, n):
    return product_fraction((x - j) / (j + 1) for j in range(n))


def finite_harmonic(b, length, word):
    return sum((product_fraction((b+n)**(-s)
                                for n, s in zip(reversed(indices), word))
                for indices in combinations(range(length), len(word))), F(0))


def main():
    counts = dict(composition=0, deconcatenation=0, top_recurrence=0,
                  finite_interval=0, reflected_interval=0,
                  multiblock_coefficients=0, insertion_identity=0)
    for depth in range(1, 7):
        roots = tuple(F(j + 2, j + 3) for j in range(depth))
        for a4, b4, c4 in [(7, 1, 5), (5, 8, 3), (11, 2, 7), (2, 7, 5)]:
            lhs = kernel(a4, b4, roots)
            rhs = sum((kernel(a4, c4, roots[:j]) *
                       kernel(c4, b4, roots[j:])
                       for j in range(depth + 1)), F(0))
            assert lhs == rhs
            counts['composition'] += 1
            rhs = sum((infinite_kernel(a4, roots[:j]) *
                       kernel(a4, b4, roots[j:])
                       for j in range(depth + 1)), F(0))
            assert infinite_kernel(b4, roots) == rhs
            counts['deconcatenation'] += 1
            if depth >= 2:
                merged = (roots[0] * roots[1],) + roots[2:]
                rhs = (roots[0]**4 * kernel(a4, b4, merged)
                       - roots[0]**a4 * kernel(a4, b4, roots[1:]))
                rhs /= 1 - roots[0]**4
                assert lhs == rhs
                counts['top_recurrence'] += 1
            inverse = sum((kernel(a4, b4, roots[:j]) *
                           kernel(b4, a4, roots[j:])
                           for j in range(depth + 1)), F(0))
            assert inverse == 0
            counts['reflected_interval'] += 1
        for length in range(0, 8):
            for b4 in (1, 3, 5):
                assert kernel(b4 + 4*length, b4, roots) == \
                    finite_kernel(b4, length, roots)
                counts['finite_interval'] += 1

    # Independent finite sums test every placement of up to six zero
    # letters among two or three surviving integral free orders.
    # A fixed free tuple contributes the product of binomial gap counts.
    for free in [(1, 2), (2, 1, 3)]:
        depth = len(free)
        for length in (4, 5, 6):
            b = F(3, 4)
            a = b + length
            for decorations in product(range(3), repeat=depth+1):
                word = []
                for j, s in enumerate(free):
                    word += [0] * decorations[j] + [s]
                word += [0] * decorations[-1]
                lhs = finite_harmonic(b, length, word)
                rhs = F(0)
                for indices in combinations(range(length), depth):
                    ys = [b+n for n in reversed(indices)]
                    gaps = [a-ys[0]-1]
                    gaps += [ys[j]-ys[j+1]-1 for j in range(depth-1)]
                    gaps += [ys[-1]-b]
                    rhs += product_fraction(binomial(g, p)
                                           for g, p in zip(gaps, decorations)) \
                        * product_fraction(y**(-s) for y, s in zip(ys, free))
                assert lhs == rhs
                counts['multiblock_coefficients'] += 1
            for total in range(5):
                lhs = F(0)
                for dec in product(range(total+1), repeat=depth+1):
                    if sum(dec) != total:
                        continue
                    word = []
                    for j, s in enumerate(free):
                        word += [0] * dec[j] + [s]
                    word += [0] * dec[-1]
                    lhs += finite_harmonic(b, length, word)
                rhs = binomial(a-b-depth, total)*finite_harmonic(b, length, free)
                assert lhs == rhs
                counts['insertion_identity'] += 1

    result = dict(status='passed', arithmetic='exact fractions',
                  counts=counts, total=sum(counts.values()),
                  scope='Finite algebra only; not an analytic or interval certificate.')
    dest = Path(sys.argv[1]) if len(sys.argv) > 1 else \
        Path(__file__).resolve().parents[1] / 'results' / 'zero_block_exact_results.json'
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
