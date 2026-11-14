#!/usr/bin/env python3
"""Replay the finite compilation-cost screens; this is not a TM certificate.

Python 3.10+, standard library only.  Run from any directory:
    python3 -B /path/to/pa194dhs/supplement/semantic_screens.py

The three frozen tree associations are expanded against the same pinned
PA196 compiler references as the main construction.  The reported cost is
raw states minus a maximum matching of eligible contextual-fold pairs.
This is optimistic: chosen folds need not be simultaneously compatible.
These profiles have no certified source simulation or blank initialization.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / 'construction'))
import compiler as c

INC = ('leaf', 'inc', 1)
c.MACROS[(INC, INC)] = 99
c.MACROS[((INC, INC), (INC, INC))] = 190
c.MACROS[('leaf', 'dec', 4)] = 144
BASE, _ = c.machine()

# Cached MP and the unsymmetric cached-head Shift test.
CACHE = {
    (38, 0): (0, True, 11), (38, 1): (1, True, 122),
    (164, 1): (1, True, 130),
    (214, 0): (0, True, 312), (214, 1): (1, True, 20),
    (312, 0): (0, True, 188),
}
SYMMETRIC = {
    **CACHE, (214, 1): (1, True, 30),
    (310, 1): (1, True, 331),
    (331, 0): (0, True, 63), (331, 1): (1, False, 73),
}
TOP_ONLY = {
    (164, 1): (1, True, 114), (38, 1): (1, True, 332),
    (332, 0): (0, True, 45), (332, 1): (1, True, 57),
    (310, 1): (1, True, 331),
    (331, 0): (0, True, 63), (331, 1): (1, False, 73),
}
MODES = {
    'old': {}, 'N': {(164, 1): (1, True, 114)},
    'C': CACHE, 'H': {**CACHE, (164, 1): (1, True, 114)},
    'CS': SYMMETRIC,
    'HS': {**SYMMETRIC, (164, 1): (1, True, 114)},
    'T': TOP_ONLY,
}
VARIABLES = ('node70', 'node55', 'node58')  # A, D, H respectively.


def normal(tree):
    if tree == 'node60':
        return INC, INC
    if tree == 'node61':
        return (INC, INC), (INC, INC)
    return tuple(map(normal, tree)) if c.isnode(tree) else tree


def fixed(grammar, changes, radix='4'):
    rows = BASE.copy()
    rows.update(changes)
    if grammar == 'D':
        rows[27, 1] = (1, True, 21)
    if radix != '4':
        rows[330, 0] = (0, True, 61)
        rows[330, 1] = (1, True, 99)
        if radix == '4R':
            rows[190, 0] = (0, True, 61)
            rows[190, 1] = (1, True, 330)
        elif radix in ('5', '6'):
            rows[190, 0] = (0, True, 330)
            rows[190, 1] = (1, True, 99 if radix == '5' else 330)
        elif radix == '8':
            rows[190, 0] = (0, True, 333)
            rows[190, 1] = (1, True, 333)
            rows[333, 0] = (0, True, 99)
            rows[333, 1] = (1, True, 99)
        else:
            raise ValueError(radix)
    return rows


def profile(tree, rows):
    c.machine = lambda: (rows, [])
    raw, _, shape = c.build(tree)
    opportunities = c.opportunities_fast(raw, {q: None for q, _ in raw})
    matching = c.max_matching(opportunities)
    return {
        'raw_states': len(raw) // 2, 'reader_states': len(shape),
        'folds': len(matching),
        'optimistic_states': len(raw) // 2 - len(matching),
        'ops': opportunities, 'matching': matching,
    }


def replace_diagonal_copies(tree, replacement):
    # In all three expanded AX layouts the three copies occupy token
    # positions 121, 122, 123, counted from zero in the 190-token word.
    index = 0

    def visit(node):
        nonlocal index
        if c.isnode(node):
            return tuple(visit(child) for child in node)
        result = replacement if 121 <= index <= 123 else node
        index += 1
        return result

    result = visit(tree)
    assert index == 190
    return result


def bump(variable, k):
    tree = variable
    for _ in range(k):
        tree = tree, INC
    return tree


def replay():
    provenance = json.loads((HERE / 'grammars/PROVENANCE.json').read_text())
    trees = {}
    for grammar in ('A', 'D', 'Q'):
        path = HERE / 'grammars' / (grammar + '.json')
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        assert digest == provenance['grammars'][grammar]['sha256']
        trees[grammar] = normal(c.read_grammar(path))

    cross, positive, negative = [], [], []
    for grammar, tree in trees.items():
        for mode, changes in MODES.items():
            for radix in ('4', '4R', '5', '6', '8'):
                data = profile(tree, fixed(grammar, changes, radix))
                cross.append({'grammar': grammar, 'mode': mode,
                              'radix': radix, **data})
        for variable in VARIABLES:
            for k in range(1, 9):
                variant = replace_diagonal_copies(tree, bump(variable, k))
                data = profile(variant, fixed(grammar, CACHE))
                positive.append({
                    'grammar': grammar, 'var': variable, 'k': k,
                    'raw': data['raw_states'], 'fold': data['folds'],
                    'cost': data['optimistic_states'],
                })
            # copyR; push; incT; cons builds N(R)=I(R,1).
            negated = (((variable, 'node49'), INC), 'node65')
            variant = replace_diagonal_copies(tree, negated)
            data = profile(variant, fixed(grammar, CACHE))
            negative.append({
                'grammar': grammar, 'variable': variable,
                'raw_states': data['raw_states'],
                'maximum_pair_matching': data['folds'],
                'optimistic_states': data['optimistic_states'],
            })
    return {'cross_screen.json': cross,
            'positive_offset_screen.json': positive,
            'negative_only_screen.json': negative}


def main():
    if not __debug__:
        raise RuntimeError('Run this replay without Python -O')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path,
                        help='optionally also save recomputed records here')
    args = parser.parse_args()
    results = replay()
    for name, actual in results.items():
        expected = json.loads((HERE / name).read_text())
        # Matchings of the same size can vary with dictionary/set ordering;
        # the replay comparison fixes every profile parameter and count.
        def counts(records):
            return [{k: v for k, v in row.items()
                     if k not in ('ops', 'matching')} for row in records]
        assert counts(actual) == counts(expected), name
        if args.output_dir is not None:
            args.output_dir.mkdir(parents=True, exist_ok=True)
            (args.output_dir / name).write_text(json.dumps(actual, indent=2) + '\n')
    receipt = {
        'status': 'PASS', 'cross_profiles': len(results['cross_screen.json']),
        'cross_minimum_optimistic_states': min(
            r['optimistic_states'] for r in results['cross_screen.json']),
        'positive_offset_profiles': len(results['positive_offset_screen.json']),
        'positive_offset_minimum_optimistic_states': min(
            r['cost'] for r in results['positive_offset_screen.json']),
        'negative_only_profiles': len(results['negative_only_screen.json']),
        'negative_only_minimum_optimistic_states': min(
            r['optimistic_states'] for r in results['negative_only_screen.json']),
        'scope': 'Optimistic finite compilation-cost screens, not accepted machines',
    }
    print(json.dumps(receipt, indent=2))
    if args.output_dir is not None:
        (args.output_dir / 'replay_receipt.json').write_text(
            json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()
