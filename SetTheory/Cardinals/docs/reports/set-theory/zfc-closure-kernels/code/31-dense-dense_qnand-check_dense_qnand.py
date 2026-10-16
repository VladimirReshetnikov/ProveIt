#!/usr/bin/env python3
"""Finite canonical, scope, semantic and size comparisons for the dense codec.

These checks support the implementation. The accompanying proof note supplies
the unbounded arithmetic induction; finite tests do not establish consistency.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from random import Random

import dense_qnand_codec as c


def bit_length(n):
    return max(1, n.bit_length())


def random_formula(rng, d, remaining):
    if remaining <= 0 or rng.randrange(4) == 0:
        return ('rel', rng.randrange(d), rng.randrange(d))
    left = rng.randrange(remaining)
    return ('q', random_formula(rng, d + 1, left),
            random_formula(rng, d + 1, remaining - left - 1))


def run():
    canonical = 0
    for d in range(1, 9):
        for n in range(12000):
            formula = c.decode(d, n)
            assert c.scoped(formula, d)
            assert c.encode(d, formula) == n
            canonical += 1

    # Code alone is NOT a valid memo key. A threshold must depend on scope.
    assert c.decode(2, 4) == ('q', ('rel', 0, 0), ('rel', 0, 0))
    assert c.decode(3, 4) == ('rel', 1, 1)

    # One binder binds index zero in BOTH children. Indices equal to d at
    # the child are legal old-slot references, not rejected or renamed.
    inner = ('q', ('rel', 1, 0), ('rel', 0, 1))
    assert c.decode(1, c.encode(1, inner)) == inner
    deeper = ('q', ('q', ('rel', 2, 0), ('rel', 1, 2)), ('rel', 1, 0))
    assert c.decode(1, c.encode(1, deeper)) == deeper

    semantic = 0
    domain = (0, 1)
    for d in range(1, 5):
        for n in range(250):
            formula = c.decode(d, n)
            for bits in range(16):
                def relation(a, b, bits=bits):
                    return bool(bits & (1 << (2 * a + b)))
                for environment in c.assignments(domain, d):
                    assert c.evaluate(formula, environment, domain, relation) == \
                           c.evaluate_number(d, n, environment, domain, relation)
                    semantic += 1

    # A corpus built from scoped syntax instead of decoder outputs checks the
    # opposite inverse and records size tradeoffs without an enumeration bias.
    rng = Random(20261016)
    comparisons = {'dense_shorter': 0, 'equal': 0, 'raw_shorter': 0}
    syntax_cases = 0
    total_dense_bits = total_raw_bits = 0
    for d in range(1, 9):
        for _ in range(256):
            formula = random_formula(rng, d, rng.randrange(1, 22))
            dense = c.encode(d, formula)
            raw = c.raw_encode(formula)
            assert c.decode(d, dense) == formula
            dense_bits, raw_bits = bit_length(dense), bit_length(raw)
            total_dense_bits += dense_bits
            total_raw_bits += raw_bits
            key = ('dense_shorter' if dense_bits < raw_bits else
                   'raw_shorter' if raw_bits < dense_bits else 'equal')
            comparisons[key] += 1
            syntax_cases += 1

    examples = []
    for d, name, formula in [
            (4, 'atom at the last free slot', ('rel', 3, 3)),
            (4, 'least compound', ('q', ('rel', 0, 0), ('rel', 0, 0))),
            (1, 'both branches use the new scope', inner),
            (1, 'two nested binders', deeper)]:
        dense, raw = c.encode(d, formula), c.raw_encode(formula)
        examples.append({'name': name, 'scope': d, 'formula': formula,
                         'dense_code': dense, 'raw_code': raw,
                         'dense_bits': bit_length(dense), 'raw_bits': bit_length(raw)})
    assert examples[0]['dense_bits'] < examples[0]['raw_bits']
    assert examples[1]['dense_bits'] > examples[1]['raw_bits']

    rejected = 0
    for call in [lambda: c.decode(0, 0), lambda: c.decode(1, -1),
                 lambda: c.decode(True, 0), lambda: c.decode(1, False),
                 lambda: c.encode(1, ('rel', 1, 0)),
                 lambda: c.encode(1, ('rel', -1, 0)),
                 lambda: c.encode(1, ('rel', True, 0))]:
        try:
            call()
        except ValueError:
            rejected += 1
        else:
            raise AssertionError('Malformed encoder/API input accepted')

    return {'canonical_roundtrips': canonical,
            'independently_evaluated_structure_assignment_cases': semantic,
            'syntax_generated_roundtrips': syntax_cases,
            'seed': 20261016,
            'bit_comparison_corpus': comparisons,
            'aggregate_dense_bits': total_dense_bits,
            'aggregate_raw_bits': total_raw_bits,
            'malformed_api_cases_rejected': rejected,
            'examples': examples,
            'interpretation': 'Finite validation only; no compiled-state advantage or consistency result.'}


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without Python assertion suppression')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('dense_qnand_results.json'))
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'examples'}, indent=2))
