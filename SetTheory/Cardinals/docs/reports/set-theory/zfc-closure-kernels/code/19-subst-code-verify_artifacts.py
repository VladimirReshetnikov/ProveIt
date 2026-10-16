#!/usr/bin/env python3
"""Reproduce semantic, logical, codec and malformed-certificate checks.

No bounded computation in this file establishes consistency or nonhalting.
Accepted examples are closed theorem demonstrations, never refutations.
"""
from __future__ import annotations

from dataclasses import replace
import itertools
import json
from pathlib import Path
import random
import sys
import unittest

import lazy_psc as L
import certificate_codec as C

ROOT = Path(__file__).resolve().parents[1]
R = lambda a, b: ('R', a, b)
I = lambda a, b: ('I', a, b)
A = lambda a: ('A', a)
B = lambda n: ('b', n)
F = lambda n: ('f', n)
N = lambda a: I(a, L.BOT)
And = lambda a, b: N(I(a, N(b)))
Iff = lambda a, b: And(I(a, b), I(b, a))


def identity_proof(pos, neg, p, n, length, counter):
    """Untrusted example producer; kernel independently checks every result."""
    pos, neg = pos.expose(), neg.expose()
    if pos.node[0] != neg.node[0]:
        raise ValueError('Different shapes in identity producer')
    op = pos.node[0]
    if op == 'B':
        return ['B', p]
    if op == 'R':
        if pos.atom() != neg.atom():
            raise ValueError('Unequal evaluated atoms in identity producer')
        return ['X', p, n]
    if op == 'A':
        child = identity_proof(pos.child(1, counter), neg.child(1, counter),
                               length + 1, length, length + 2, counter + 1)
        return ['A-', n, ['A+', p, counter, child]]
    # Expand the negative implication first, then the positive one.
    left = identity_proof(neg.child(1), pos.child(1), length, length + 2,
                          length + 3, counter)
    right = identity_proof(pos.child(2), neg.child(2), length + 2, length + 1,
                           length + 3, counter)
    return ['I-', n, ['I+', p, left, right]]


def bind_free(f, label, depth=0):
    """Close one selected free parameter with a new outer universal."""
    def v(t):
        return B(depth) if t == F(label) else t
    if f[0] == 'R':
        return R(v(f[1]), v(f[2]))
    if f[0] == 'I':
        return I(bind_free(f[1], label, depth), bind_free(f[2], label, depth))
    if f[0] == 'A':
        return A(bind_free(f[1], label, depth + 1))
    return L.BOT


def examples():
    ui = A(A(I(A(R(B(0), B(2))), R(B(0), B(1)))))
    ui_cert = {'matrices': [], 'proof':
               ['A-', 0, ['A-', 1, ['I-', 2, ['A+', 3, 2, ['X', 5, 4]]]]]}

    def composite(x, y, z):
        return Iff(Iff(R(x, y), R(x, z)), R(y, z))
    source = composite(B(0), B(2), B(1))
    collided = composite(B(1), B(1), B(0))
    collision_ui = A(A(I(A(source), collided)))
    pos = L.Closure(False, source, (1, 2, 1))
    neg = L.Closure(False, collided, (2, 1))
    collision_proof = ['A-', 0, ['A-', 1, ['I-', 2,
        ['A+', 3, 1, identity_proof(pos, neg, 5, 4, 6, 3)]]]]
    collision_cert = {'matrices': [], 'proof': collision_proof}

    # This matrix has an internal quantifier and a genuine free parameter.
    matrix = I(R(F(0), F(2)), A(I(R(B(0), F(1)), R(F(0), B(0)))))
    expanded = L.materialize(matrix)
    theorem = A(bind_free(expanded, 0))
    # The negative universal creates p1. Only THEN does AX instantiate f2=p1.
    lazy = L.Closure(True, L.TEMPLATE, (), L.Root(matrix, ((2, 1),)))
    ordinary = L.Closure(False, theorem[1], (1,))
    ax_proof = ['A-', 0, ['AX', 0, [[2, 1]],
                 identity_proof(lazy, ordinary, 2, 1, 3, 2)]]
    ax_cert = {'matrices': [matrix], 'proof': ax_proof}
    return {'universal_instantiation': (ui_cert, ui),
            'colliding_instantiation': (collision_cert, collision_ui),
            'late_parameter_schema': (ax_cert, theorem)}


EXAMPLES = examples()


def random_formula(rng, depth, budget):
    if budget <= 0:
        if rng.randrange(6) == 0:
            return L.BOT
        def var():
            if depth and rng.randrange(3) == 0:
                return B(rng.randrange(depth))
            return F(rng.randrange(6))
        return R(var(), var())
    tag = rng.randrange(4)
    if tag == 0:
        return A(random_formula(rng, depth + 1, budget - 1))
    if tag < 3:
        return I(random_formula(rng, depth, budget - 1),
                 random_formula(rng, depth, budget - 1))
    return random_formula(rng, depth, 0)


def matrix_eval(f, relation, x, y, params, bound=()):
    """Direct relation-matrix oracle independent of lazy closure evaluation."""
    def value(v):
        if v[0] == 'b':
            return bound[v[1]]
        if v[1] == 0:
            return x
        if v[1] == 1:
            return y
        return params.get(v[1], 0)
    if f[0] == 'B':
        return False
    if f[0] == 'R':
        return relation[value(f[1])][value(f[2])]
    if f[0] == 'I':
        return not matrix_eval(f[1], relation, x, y, params, bound) or matrix_eval(f[2], relation, x, y, params, bound)
    return all(matrix_eval(f[1], relation, x, y, params, (z,) + bound)
               for z in range(len(relation)))


def direct_psc(matrix, relation, params):
    """Literal mathematical PSC, with a precomputed finite matrix extension."""
    n = len(relation)
    rho = [[matrix_eval(matrix, relation, x, y, params) for y in range(n)]
           for x in range(n)]
    sub = [[all(not relation[z][x] or relation[z][b] for z in range(n))
            for b in range(n)] for x in range(n)]
    bounded = all(any(all(not rho[x][y] or sub[y][b] for y in range(n))
                      for b in range(n)) for x in range(n))
    if not bounded:
        return True
    return all(any(
        all(not ((sub[x][a] or relation[x][h]) and rho[x][y]) or relation[y][h]
            for x in range(n) for y in range(n))
        and all(not relation[y][h] or any(rho[x][y] for x in range(n))
                for y in range(n))
        for h in range(n)) for a in range(n))


def semantic_regressions():
    rng = random.Random(20261016)
    matrices = [L.BOT, I(L.BOT, L.BOT), R(F(0), F(1)), R(F(1), F(0)),
                R(F(2), F(3)), A(R(B(0), F(0))),
                A(A(I(R(B(0), B(1)), R(F(1), F(2)))))]
    matrices += [random_formula(rng, 0, 3) for _ in range(17)]
    count = 0
    values = {'true': 0, 'false': 0}
    for n in (1, 2, 3):
        masks = range(1 << (n*n)) if n < 3 else sorted({0, 511, *[rng.randrange(512) for _ in range(64)]})
        for mask in masks:
            relation = tuple(tuple(bool(mask & (1 << (n*x+y))) for y in range(n))
                             for x in range(n))
            for matrix in matrices:
                params = tuple((j, rng.randrange(n)) for j in range(2, 6))
                lazy = L.evaluate(L.Closure(True, L.TEMPLATE, (), L.Root(matrix, params)), relation)
                expanded = L.ordinary_eval(L.materialize(matrix, params), relation)
                direct = direct_psc(matrix, relation, dict(params))
                if lazy != expanded or expanded != direct:
                    raise AssertionError(('Template semantic disagreement', n, mask, matrix, params))
                values[str(lazy).lower()] += 1
                count += 1
    return {'cases': count, 'matrices': len(matrices), 'domain_sizes': [1, 2, 3],
            'three_way_agreement': True, 'truth_distribution': values}


class CheckerTests(unittest.TestCase):
    def test_accepted_examples(self):
        for cert, target in EXAMPLES.values():
            result = L.check(cert, theorem=target)
            self.assertTrue(result['valid'])
            self.assertFalse(result['refutation'])

    def test_search_cannot_import_demo_target(self):
        for cert, target in EXAMPLES.values():
            with self.assertRaises(ValueError):
                L.check(cert)
            forged = dict(cert, theorem=target)
            with self.assertRaises(ValueError):
                L.check(forged)

    def test_future_axiom_parameter_rejected(self):
        cert = {'matrices': [L.BOT], 'proof': ['AX', 0, [[2, 1]], ['B', 0]]}
        with self.assertRaisesRegex(ValueError, 'unallocated'):
            L.check(cert)

    def test_future_gamma_parameter_rejected(self):
        cert, target = EXAMPLES['universal_instantiation']
        bad = json.loads(json.dumps(cert))
        bad['proof'][2][2][2][2] = 3
        with self.assertRaisesRegex(ValueError, 'allocated'):
            L.check(bad, theorem=target)

    def test_repeated_gamma_parameter_is_required(self):
        cert, target = EXAMPLES['colliding_instantiation']
        bad = json.loads(json.dumps(cert))
        bad['proof'][2][2][2][2] = 2  # x:=z instead of x:=y
        with self.assertRaises(ValueError):
            L.check(bad, theorem=target)

    def test_duplicate_reserved_and_boolean_maps(self):
        for env in ([[2, 0], [2, 0]], [[0, 0]], [[True, 0]], [[2, True]], [[2, -1]]):
            with self.assertRaises(ValueError):
                L.parameter_map(env, 1)

    def test_private_holes_and_unscoped_indices(self):
        for formula in (('H', 0, 1), R(B(0), F(0)), A(R(B(1), B(0)))):
            with self.assertRaises(ValueError):
                L.parse(formula)

    def test_sign_and_reference_checks(self):
        for proof in (['B', 0], ['X', 0, 0], ['B', 1], ['I-', 0, ['B', 0]], ['A+', 0, 0, ['B', 0]], ['axiom', 0]):
            with self.assertRaises(ValueError):
                L.check({'matrices': [], 'proof': proof})

    def test_matrix_stack_is_reset(self):
        matrix = A(R(B(0), F(0)))
        q = L.Closure(True, ('H', 1, 0), (2, 1, 3), L.Root(matrix, ((2, 0),))).expose()
        self.assertEqual(q.bound, ())
        self.assertEqual(q.slots, (1, 2))
        self.assertIs(q.node, matrix)
        self.assertEqual(q.child(1, 4).atom(), (4, 1))

    def test_all_three_calls_share_matrix(self):
        matrix = A(R(B(0), F(0)))
        root = L.Root(matrix)
        for call in (('H', 2, 0), ('H', 1, 0), ('H', 0, 1)):
            self.assertIs(L.Closure(True, call, (0, 1, 2), root).expose().node, matrix)

    def test_late_map_is_immutable_and_default_total(self):
        root = L.Root(R(F(2), F(99)), ((2, 1),))
        q = L.Closure(False, root.matrix, (), root, (4, 4))
        self.assertEqual(q.atom(), (1, 0))
        self.assertEqual(replace(q, bound=(5,)).atom(), (1, 0))

    def test_size_identity(self):
        for m in (L.BOT, R(F(0), F(1)), A(R(B(0), F(0))), EXAMPLES['late_parameter_schema'][0]['matrices'][0]):
            self.assertEqual(L.size(L.materialize(m)), 3*L.size(m) + 45)


def codec_regressions():
    for n in range(10000):
        if C.pair(*C.unpair(n)) != n:
            raise AssertionError('Pair roundtrip')
        if C.encode_list(C.decode_list(n)) != n:
            raise AssertionError('List roundtrip')
        if C.encode_formula(C.decode_formula(n)) != n:
            raise AssertionError('Formula roundtrip')
        if C.encode_proof(C.decode_proof(n)) != n:
            raise AssertionError('Proof roundtrip')
        if C.encode(C.decode(n)) != n:
            raise AssertionError('Certificate roundtrip')
    return {'codes_per_family': 10000, 'families': 5, 'all_roundtrips': True}


def main():
    (ROOT/'evidence').mkdir(exist_ok=True)
    (ROOT/'examples').mkdir(exist_ok=True)
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(CheckerTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)
    example_results = {}
    for name, (cert, target) in EXAMPLES.items():
        (ROOT/'examples'/f'{name}.json').write_text(json.dumps(cert, indent=2)+'\n')
        (ROOT/'examples'/f'{name}_theorem.json').write_text(json.dumps(target, indent=2)+'\n')
        example_results[name] = L.check(cert, theorem=target)
    semantics = semantic_regressions()
    codec = codec_regressions()
    diagnostic = C.search(10000)
    evidence = {'unit_tests': result.testsRun, 'all_tests_passed': True,
                'semantic_regressions': semantics, 'codec_regressions': codec,
                'bounded_search': diagnostic, 'examples': example_results,
                'template_nodes_with_holes': L.size(L.TEMPLATE),
                'matrix_holes': 3, 'wrapper_nodes_excluding_holes': 45,
                'expanded_occurrences': '45 + 3*m',
                'lazy_unshared_syntax_occurrences': '48 + m',
                'new_binary_tm_supplied': False, 'new_state_bound_claimed': False,
                'python_execution_formally_verified': False}
    (ROOT/'evidence'/'verification.json').write_text(json.dumps(evidence, indent=2, sort_keys=True)+'\n')
    print(json.dumps(evidence, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
