#!/usr/bin/env python3
"""Reproduce the independent direct-semantics review of lazy_psc.

When this file is copied beside lazy_psc.py, run:
    python independent_review.py --output ../evidence/independent-review.json

The PSC wrapper below is evaluated directly from its mathematical quantifiers;
it does not use lazy_psc.make_template(), materialize(), or ordinary_eval().
The tested side does use lazy_psc.evaluate() and its shared template closures.
This is finite diagnostic evidence, not a proof of soundness or completeness.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import random

import lazy_psc as p


SEED = 170106


def generated_matrix(rng, depth=0, fuel=4):
    if fuel == 0 or rng.random() < 0.35:
        def term():
            if depth and rng.random() < 0.45:
                return 'b', rng.randrange(depth)
            return 'f', rng.randrange(4)
        return ('B',) if rng.random() < 0.12 else ('R', term(), term())
    if rng.random() < 0.5:
        return 'A', generated_matrix(rng, depth + 1, fuel - 1)
    return ('I', generated_matrix(rng, depth, fuel - 1),
            generated_matrix(rng, depth, fuel - 1))


def direct_phi(f, relation, x, y, parameters, local=()):
    """Independent semantics of one matrix with explicit input/output values."""
    def value(t):
        if t[0] == 'b':
            return local[t[1]]
        if t[1] == 0:
            return x
        if t[1] == 1:
            return y
        return parameters.get(t[1], 0)
    if f[0] == 'B':
        return False
    if f[0] == 'R':
        return relation[value(f[1])][value(f[2])]
    if f[0] == 'I':
        return (not direct_phi(f[1], relation, x, y, parameters, local)
                or direct_phi(f[2], relation, x, y, parameters, local))
    if f[0] == 'A':
        return all(direct_phi(f[1], relation, x, y, parameters, (z,) + local)
                   for z in range(len(relation)))
    raise ValueError('Unknown matrix constructor')


def direct_wrapper(f, relation, parameters):
    """SB(phi) implies seed/hull closure and unrestricted image support."""
    universe = range(len(relation))
    subset = lambda x, a: all(not relation[z][x] or relation[z][a]
                              for z in universe)
    phi = lambda x, y: direct_phi(f, relation, x, y, parameters)
    subset_bounded = all(
        any(all(not phi(x, y) or subset(y, b) for y in universe)
            for b in universe)
        for x in universe)
    hulls = all(
        any(
            all(not (subset(x, a) or relation[x][h])
                or all(not phi(x, y) or relation[y][h] for y in universe)
                for x in universe)
            and all(not relation[y][h] or any(phi(x, y) for x in universe)
                    for y in universe)
            for h in universe)
        for a in universe)
    return not subset_bounded or hulls


def require_value_error(call, description):
    try:
        call()
    except ValueError:
        return
    raise AssertionError(description)


def run_review():
    rng = random.Random(SEED)
    rel = lambda x, y: ('R', x, y)
    forall = lambda f: ('A', f)
    implies = lambda f, g: ('I', f, g)
    f0, f1, f2 = ('f', 0), ('f', 1), ('f', 2)
    b0, b1 = ('b', 0), ('b', 1)
    matrices = [p.BOT, rel(f0, f1), forall(rel(b0, f1)),
                forall(implies(rel(b0, f2), forall(rel(b1, f0))))]
    matrices += [generated_matrix(rng) for _ in range(80)]
    comparisons = 0
    domains = []
    for n in (1, 2, 3):
        masks = list(range(2 ** (n * n))) if n <= 2 else rng.sample(range(512), 16)
        count_before = comparisons
        for mask in masks:
            relation = tuple(tuple(bool(mask & (1 << (i * n + j)))
                                   for j in range(n)) for i in range(n))
            for matrix in matrices:
                p.parse(matrix)
                for assignments in ((), ((2, n - 1),), ((2, 0), (3, n - 1))):
                    root = p.Root(matrix, assignments)
                    actual = p.evaluate(p.Closure(True, p.TEMPLATE, (), root), relation)
                    expected = direct_wrapper(matrix, relation, dict(assignments))
                    if actual != expected:
                        raise AssertionError(dict(domain=n, mask=mask, matrix=matrix,
                                                  parameters=assignments,
                                                  shared=actual, direct=expected))
                    comparisons += 1
        domains.append(dict(size=n, relation_masks=masks,
                            relation_count=len(masks),
                            comparisons=comparisons - count_before))

    a = ['A', ['R', ['b', 0], ['b', 0]]]
    identity = ['I', a, a]
    certificate = {'matrices': [],
                   'proof': ['I-', 0, ['A-', 2, ['A+', 1, 1, ['X', 3, 4]]]]}
    if not p.check(certificate, theorem=identity)['valid']:
        raise AssertionError('Valid delta/gamma identity certificate rejected')
    require_value_error(lambda: p.check({'matrices': [], 'proof': ['B', 0]}),
                        'Negative Bottom closed')
    require_value_error(lambda: p.check(
        {'matrices': [], 'proof': ['I-', 0, ['A-', 2, ['A+', 1, 2, ['X', 3, 4]]]]},
        theorem=identity), 'Unallocated gamma constant accepted')
    malformed = [['H', 0, 1], ['R', ['b', 0], ['f', 1]],
                 ['R', ['f', True], ['f', 0]]]
    for bad in malformed:
        require_value_error(lambda bad=bad: p.check({'matrices': [bad], 'proof': ['B', 0]}),
                            'Malformed source accepted')
    if comparisons != 8568:
        raise AssertionError('Unexpected comparison count')
    source = Path(p.__file__).resolve()
    return dict(
        status='PASS', seed=SEED, semantic_comparisons=comparisons,
        matrix_count=len(matrices), fixed_matrix_count=4, generated_matrix_count=80,
        parameter_maps_per_matrix_relation=3, domains=domains,
        logical_and_rejection_probes=6,
        logical_probes=[
            'Accept closed universal identity using a delta witness and gamma reuse',
            'Reject negative-Bottom closure',
            'Reject unallocated gamma parameter',
            'Reject private template hole H',
            'Reject unbound source de Bruijn index',
            'Reject Boolean numeric code'],
        checked_source_name=source.name,
        checked_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        independent_reference='direct_phi and direct_wrapper; no materialize or ordinary_eval',
        scope='Finite semantic and parser/rule probes; not a kernel proof, complete enumeration, or binary TM verification')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optionally save the printed JSON evidence')
    args = parser.parse_args()
    result = run_review()
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding='utf-8')
    print(rendered, end='')


if __name__ == '__main__':
    main()
