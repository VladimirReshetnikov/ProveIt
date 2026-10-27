#!/usr/bin/env python3
"""Finite exact checks of collision variance; not a SAT solver or asymptotic proof.

Only the Python standard library is needed. All checks use exact arithmetic.
Run from any directory; JSON is written to the bundle's results directory.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def variance_formula(edges, labels):
    m = len(edges)
    parallel = sum(a == b for a in edges for b in edges)
    single = sum((a[0] == b[0]) ^ (a[1] == b[1])
                 for a in edges for b in edges)
    return (parallel * (1 - Fraction(1, labels**2))
            + single * (Fraction(1, labels) - Fraction(1, labels**2)))


def enumerate_variance(edges, labels):
    left = sorted({e[0] for e in edges})
    right = sorted({e[1] for e in edges})
    m = len(edges)
    total = Fraction(0)
    number = 0
    minimum = None
    for values in product(range(labels), repeat=len(left) + len(right)):
        ls = dict(zip(left, values[:len(left)]))
        rs = dict(zip(right, values[len(left):]))
        loads = Counter((ls[u], rs[v]) for u, v in edges)
        # Sum (X_gamma - M / R^2)^2 over all R^2 label pairs.
        deviation = sum(x*x for x in loads.values()) - Fraction(m*m, labels**2)
        total += deviation
        minimum = deviation if minimum is None else min(minimum, deviation)
        number += 1
    return total / number, number, minimum


def main():
    samples = []
    # Every nonempty 2-by-2 bipartite multigraph with edge multiplicities 0,1,2.
    choices = [(0, 0), (0, 1), (1, 0), (1, 1)]
    total_labelings = 0
    for multiplicities in product(range(3), repeat=4):
        edges = [edge for edge, count in zip(choices, multiplicities)
                 for _ in range(count)]
        if not edges:
            continue
        for labels in (2, 3):
            mean, number, minimum = enumerate_variance(edges, labels)
            formula = variance_formula(edges, labels)
            require(mean == formula, ('variance identity', edges, labels, mean, formula))
            degree = max(list(Counter(u for u, _ in edges).values())
                         + list(Counter(v for _, v in edges).values()))
            mu = max(Counter(edges).values())
            refined = len(edges) * mu + Fraction(2*len(edges)*degree, labels)
            coarse = 2*len(edges)*degree
            require(mean <= refined, ('refined bound', edges, labels))
            require(mean <= coarse, ('coarse bound', edges, labels))
            require(minimum <= mean, 'conditional-expectation existence')
            total_labelings += number
            samples.append({'multiplicities': multiplicities, 'R': labels,
                            'mean_numerator': mean.numerator,
                            'mean_denominator': mean.denominator})
    result = {'status': 'pass', 'graph_label_count_cases': len(samples),
              'labelings_enumerated': total_labelings,
              'scope': 'Exact finite variance identities and bounds only.',
              'samples': samples}
    output = Path(__file__).resolve().parents[1] / 'results' / 'packing_checks.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'samples'}, indent=2))


if __name__ == '__main__':
    main()
