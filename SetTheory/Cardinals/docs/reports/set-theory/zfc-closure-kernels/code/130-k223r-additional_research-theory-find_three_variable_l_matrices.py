#!/usr/bin/env python3
"""Exhaustive two- and three-element MP matrices for identifications in L.

Any returned matrix is a concrete pure implicational obstruction. Absence
of a small matrix is not a proof of completeness. Quantifier and equality
rows are outside this search's scope.
"""
import itertools
import json
from pathlib import Path
import time

VARIABLES = ('a', 'b', 'c', 'u')
PAIRS = tuple(itertools.combinations(VARIABLES, 2))


def check_matrix(table, size, designated, pair):
    def imp(x, y):
        return table[size * x + y]
    def luk(a, b, c, u):
        return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))
    if any(x in designated and imp(x, y) in designated and y not in designated
           for x, y in itertools.product(range(size), repeat=2)):
        return None
    free = [v for v in VARIABLES if v != pair[1]]
    for values in itertools.product(range(size), repeat=3):
        valuation = dict(zip(free, values))
        valuation[pair[1]] = valuation[pair[0]]
        if luk(*(valuation[v] for v in VARIABLES)) not in designated:
            return None
    for a, b, c in itertools.product(range(size), repeat=3):
        targets = {
            'K': imp(a, imp(b, a)),
            'S': imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c))),
            'Peirce': imp(imp(imp(a, b), a), a),
        }
        for name, value in targets.items():
            if value not in designated:
                return {'axiom_identification': f'{pair[1]}={pair[0]}',
                        'size': size, 'designated': sorted(designated),
                        'implication_rows': [list(table[size*i:size*(i+1)])
                                             for i in range(size)],
                        'failed_classical_theorem': name,
                        'countervaluation': {'a': a, 'b': b, 'c': c},
                        'theorem_value': value}
    return None


def search():
    start = time.monotonic()
    remaining = set(PAIRS)
    found = {}
    matrix_count = {}
    for n in (2, 3):
        for k in range(1, n):
            designated = frozenset(range(n-k, n))
            options = [tuple(v for v in range(n)
                             if not (x in designated and y not in designated
                                     and v in designated))
                       for x, y in itertools.product(range(n), repeat=2)]
            count = 0
            for table in itertools.product(*options):
                count += 1
                for pair in tuple(remaining):
                    result = check_matrix(table, n, designated, pair)
                    if result is not None:
                        found[pair] = result
                        remaining.remove(pair)
                        print(json.dumps(result), flush=True)
            matrix_count[f'n={n},designated={k}'] = count
    result = {
        'scope': 'Pure implication with substitution and modus ponens only.',
        'original_L': '((c -> u) -> a) -> ((a -> c) -> (b -> c))',
        'countermodels': [found[p] for p in PAIRS if p in found],
        'not_resolved_by_small_matrices': [f'{q}={p}' for p, q in PAIRS
                                          if (p, q) in remaining],
        'examined_matrices': matrix_count,
        'seconds': time.monotonic() - start,
        'interpretation': 'Each countermodel proves the identified single axiom cannot derive the indicated classical theorem. Unresolved cases need further work. No claim about the entire K calculus is made.'
    }
    out = Path(__file__).parent / 'evidence' / 'three_variable_l_matrices.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    search()
