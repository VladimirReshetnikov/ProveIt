#!/usr/bin/env python3
"""Eight propositionally equivalent PA196 gate spellings.

The source words use experiments/words.py's node names and stack convention.
This certifies local Boolean equivalences and transcription, not a TM compiler.
"""
import argparse
import itertools
import json
from pathlib import Path

ONE = '1'
INC = ('leaf', 'inc', 1)
TOK = {'D': 'node55', 'H': 'node58', 'A': 'node70'}

def C(tag, a, b): return (tag, a, b)
def I(a, b): return C(0, a, b)
def M(a, b): return C(1, a, b)
def U(a, b): return C(2, b, a)
def E(a, b, flip=False): return C(3, b, a) if flip else C(3, a, b)
def N(a): return I(a, ONE)
def And(a, b): return N(I(a, N(b)))

def emit(f):
    if isinstance(f, str):
        return ['node49', INC] if f == ONE else [TOK[f]]
    tag, a, b = f
    return emit(a) + emit(b) + ['node65'] + [INC] * tag

def gate(commute, conjunct_swap, gate_swap, equality_flip=False):
    a, b, c = 'HDA'
    atom = E(a, b, equality_flip)
    delta = I(atom, U(c, atom))
    atom = M(a, b)
    vacuity = I(atom, U(c, atom))
    point = I(c, M(c, b))
    x, p, y = M(a, b), c, M(c, b)
    left = I(p, I(x, y)) if commute else I(x, I(p, y))
    right = I(y, p)
    matrix = And(right, left) if conjunct_swap else And(left, right)
    separation = U(b, matrix)
    q = U(c, I(separation, N(point)))
    return N(I(vacuity, I(delta, q))) if gate_swap else N(I(delta, I(vacuity, q)))

def imp(a, b): return (not a) or b

def check_boolean_equivalence():
    checks = 0
    for x, p, y in itertools.product((False, True), repeat=3):
        old = imp(x, imp(p, y)) and imp(y, p)
        for commute, swap in itertools.product((False, True), repeat=2):
            left = imp(p, imp(x, y)) if commute else imp(x, imp(p, y))
            right = imp(y, p)
            new = (right and left) if swap else (left and right)
            assert old == new
            checks += 1
    for delta, v, q in itertools.product((False, True), repeat=3):
        assert (not imp(delta, imp(v, q))) == (not imp(v, imp(delta, q)))
        checks += 1
    return checks

def minimum_implication_matrix():
    """Enumerate all minimum-tree formulas over X,P,Y,false,true.

    Dynamic programming by Boolean function is complete for this additive
    tree-size objective: a minimum formula has minimum-size children.
    """
    vals = list(itertools.product((False, True), repeat=3))
    def mask(f): return sum(int(f(*v)) << i for i, v in enumerate(vals))
    x, p, y = [mask(lambda *v, i=i: v[i]) for i in range(3)]
    target = mask(lambda x,p,y: imp(x, imp(p,y)) and imp(y,p))
    best = {0: (0, {'F'}), 255: (0, {'T'}),
            x: (0, {'X'}), p: (0, {'P'}), y: (0, {'Y'})}
    layers = []
    for cost in range(1, 7):
        out = {}
        for a, (ca, fa) in list(best.items()):
            for b, (cb, fb) in list(best.items()):
                c = ((~a) | b) & 255
                if ca + cb + 1 != cost or c in best:
                    continue
                out.setdefault(c, set()).update('(' + s + '>' + t + ')'
                                                for s in fa for t in fb)
        best.update({c: (cost, fs) for c, fs in out.items()})
        layers.append({'cost': cost, 'new_functions': len(out),
                       'minimum_formulas': sum(map(len, out.values()))})
    assert best[target][0] == 6
    assert len(best[target][1]) == 4
    return {'minimum_implications': 6,
            'minimum_formulas': sorted(best[target][1]), 'layers': layers}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    variants = []
    for flags in itertools.product((False, True), repeat=3):
        records = {str(flip).lower(): emit(gate(*flags, equality_flip=flip))
                   for flip in (False, True)}
        assert all(len(word) == 77 for word in records.values())
        variants.append({'commute_matrix_antecedents': flags[0],
                         'swap_matrix_conjuncts': flags[1],
                         'swap_gate_vacuities': flags[2],
                         'words_by_equality_flip': records})
    result = {'boolean_checks': check_boolean_equivalence(),
              'matrix_minimum': minimum_implication_matrix(),
              'scope': 'Local propositional equivalence; no machine or PA theorem asserted.',
              'variants': variants}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'variants': len(variants), 'word_length': len(emit(gate(False,False,False))),
                      'boolean_checks': result['boolean_checks']}))

if __name__ == '__main__': main()
