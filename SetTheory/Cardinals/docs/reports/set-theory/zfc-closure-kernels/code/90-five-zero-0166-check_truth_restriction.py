#!/usr/bin/env python3
"""A finite-matrix obstruction to fixing Lukasiewicz's fourth input to truth.

This is a propositional obstruction, not a countermodel to CP plus GIC.
No third-party dependency is used.
"""
from itertools import product
import argparse, json
from pathlib import Path

V = range(3)
TRUE, FALSE = 2, 0
def imp(a, b): return min(TRUE, TRUE - a + b)
def neg(a): return imp(a, FALSE)
def L(a, b, c, u): return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))
def K(a, b): return imp(a, imp(b, a))
def S(a, b, c): return imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).parent/'codec-source-results/truth-restriction-matrix.json')
    args=parser.parse_args()
    assert all(imp(TRUE, b) == b for b in V)  # Modus ponens preserves designation.
    checks = {
        'restricted_L': all(L(a, b, c, TRUE) == TRUE for a, b, c in product(V, repeat=3)),
        'K': all(K(a, b) == TRUE for a, b in product(V, repeat=2)),
        'ex_falso': all(imp(FALSE, a) == TRUE for a in V),
        'double_negation_elimination': all(imp(neg(neg(a)), a) == TRUE for a in V),
    }
    assert all(checks.values())
    failures = [{'a': a, 'b': b, 'c': c, 'value': S(a, b, c)}
                for a, b, c in product(V, repeat=3) if S(a, b, c) != TRUE]
    assert {'a': 1, 'b': 1, 'c': 0, 'value': 1} in failures
    result = {
        'status': 'PASS', 'values': list(V), 'designated': [TRUE],
        'implication_table': [[imp(a, b) for b in V] for a in V],
        'validated_axioms': checks, 'S_countervaluations': failures,
        'conclusion': 'The truth-restricted L schema, even with K, ex falso and DNE, does not derive S under substitution and modus ponens.',
        'scope': 'Propositional calculus only; no claim about full first-order CP/GIC theory.',
    }
    target = args.output
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
