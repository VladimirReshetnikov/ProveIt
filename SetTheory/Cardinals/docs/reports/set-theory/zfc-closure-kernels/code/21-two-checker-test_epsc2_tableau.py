#!/usr/bin/env python3
"""Independent expansion, direct semantics, and adversarial checker regressions.

The expansion routines in this test file are not part of the runtime checker.
Tests are finite evidence; the accompanying notes give general mathematical
arguments. No successful test is a refutation of EPSC2.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
import json
from pathlib import Path

import epsc2_tableau as t


def instantiate(phi, projection, depth=0):
    """Independent ordinary de Bruijn expansion of one matrix occurrence."""
    tag = phi[0]
    if tag == 'rel':
        def index(i):
            return i if i < depth else depth + projection[i - depth]
        return t.Rel(index(phi[1]), index(phi[2]))
    if tag == 'all':
        return t.All(instantiate(phi[1], projection, depth + 1))
    if tag == 'imp':
        return t.Imp(instantiate(phi[1], projection, depth),
                     instantiate(phi[2], projection, depth))
    return t.BOT


def expanded(template, matrix):
    tag = template[0]
    if tag == 'hole':
        return instantiate(matrix, template[1:])
    if tag == 'all':
        return t.All(expanded(template[1], matrix))
    if tag == 'imp':
        return t.Imp(expanded(template[1], matrix), expanded(template[2], matrix))
    return template


def evaluate(entry, relation, size):
    e = entry.exposed()
    tag = e.formula[0]
    if tag == 'bot':
        return False
    if tag == 'rel':
        x, y = e.atom()
        return bool(relation & (1 << (size * x + y)))
    if tag == 'imp':
        return (not evaluate(e.child(e.formula[1]), relation, size)
                or evaluate(e.child(e.formula[2]), relation, size))
    return all(evaluate(e.child(e.formula[1], environment=(value,) + e.environment),
                        relation, size) for value in range(size))


def direct_epsc(matrix, relation, size):
    """The literal set-theoretic EPSC2 definition, without template indices."""
    domain = range(size)
    mem = lambda x, y: bool(relation & (1 << (size * x + y)))
    subset = lambda y, b: all(not mem(z, y) or mem(z, b) for z in domain)
    empty = lambda x: all(not mem(z, x) for z in domain)
    for p, q in product(domain, repeat=2):
        rho = lambda x, y: evaluate(t.Entry(True, matrix, (x, y, p, q)), relation, size)
        premise = all(any(all(not rho(x, y) or subset(y, b) for y in domain)
                          for b in domain) for x in domain)
        if premise and not any(
            all(not ((empty(x) or mem(x, c)) and rho(x, y)) or mem(y, c)
                for x, y in product(domain, repeat=2))
            and all(not mem(y, c) or any(rho(x, y) for x in domain) for y in domain)
            for c in domain):
            return False
    return True


def identity(entry, positive=0, negative=1, length=2, fresh=1):
    """Construct A, not A demonstrations; this generator is not trusted."""
    e = entry.exposed()
    tag = e.formula[0]
    if tag == 'bot':
        return ['bottom', positive]
    if tag == 'rel':
        return ['close', positive, negative]
    if tag == 'all':
        child = e.child(e.formula[1], environment=(fresh,) + e.environment)
        rest = identity(child, length + 1, length, length + 2, fresh + 1)
        return ['all', negative, ['all', positive, fresh, rest]]
    left = identity(e.child(e.formula[1]), length, length + 2, length + 3, fresh)
    right = identity(e.child(e.formula[2]), length + 2, length + 1, length + 3, fresh)
    return ['imp', negative, ['imp', positive, left, right]]


def expect_reject(thunk):
    try:
        thunk()
    except ValueError:
        return
    raise AssertionError('An invalid certificate was accepted')


def matrices():
    atoms = [t.Rel(i, j) for i, j in product(range(4), repeat=2)]
    result = [t.BOT] + atoms
    result += [t.All(t.Rel(i, j)) for i, j in product(range(5), repeat=2)]
    result += [t.All(t.All(t.Rel(i, j))) for i, j in product(range(6), repeat=2)]
    result += [t.Imp(a, b) for a, b in product(atoms[:8], repeat=2)]
    result += [t.All(t.Imp(t.Rel(0, 3), t.Rel(2, 4))),
               t.All(t.All(t.Imp(t.Rel(0, 3), t.Rel(1, 5)))),
               t.Imp(t.All(t.Rel(0, 1)), t.All(t.Rel(0, 4)))]
    return result


def run():
    if not __debug__:
        raise RuntimeError('Run this audit without -O or -OO')
    assert t.scoped(t.TEMPLATE, 0)
    forms = matrices()
    semantic_cases = differential_cases = identity_cases = 0
    for matrix in forms:
        assert t.scoped(matrix, 4)
        virtual = t.axiom(matrix)
        literal = expanded(t.TEMPLATE, matrix)
        assert t.scoped(literal, 0)
        proof = identity(virtual)
        roots = [virtual, t.Entry(False, t.TEMPLATE, (), matrix)]
        vr = t.check_tree(roots, proof)
        er = t.check_tree([t.Entry(True, literal), t.Entry(False, literal)], proof)
        assert vr['actions'] == er['actions']
        assert vr['closed_branches'] == er['closed_branches']
        identity_cases += 1
        for size in (1, 2):
            for relation in range(1 << (size * size)):
                observed = evaluate(virtual, relation, size)
                assert observed == evaluate(t.Entry(True, literal), relation, size)
                assert observed == direct_epsc(matrix, relation, size)
                semantic_cases += 1
        # Exercise distinct matrix environments directly, rather than relying
        # only on full-schema implications that might have false antecedents.
        for env in product(range(2), repeat=5):
            for projection in ((2, 0, 4, 3), (1, 0, 4, 3), (0, 1, 4, 3)):
                for relation in (0, 1, 6, 9, 15):
                    virtual_hole = t.Entry(True, t.Hole(*projection), env, matrix)
                    literal_hole = t.Entry(True, instantiate(matrix, projection), env)
                    assert evaluate(virtual_hole, relation, 2) == evaluate(literal_hole, relation, 2)
                    differential_cases += 1

    # This ordinary cross-variable specialization is false in the incoming
    # finite-sort countermodel (at v1=5); the complete checker proves it.
    transport = t.All(t.All(t.Imp(t.All(t.Rel(0, 2)), t.Rel(0, 1))))
    transport_proof = ['all', 0, ['all', 1, ['imp', 2,
                            ['all', 3, 2, ['close', 5, 4]]]]]
    t.check_tree([t.Entry(False, transport)], transport_proof)
    # Same-variable specialization rejects the constant-true-universal control.
    bottom_spec = t.Imp(t.All(t.BOT), t.BOT)
    bottom_proof = ['imp', 0, ['all', 1, 0, ['bottom', 3]]]
    t.check_tree([t.Entry(False, bottom_spec)], bottom_proof)
    # Atomic identity is identity of interpreted parameter pairs.
    t.check_tree([t.Entry(True, t.Rel(0, 1), (0, 1)),
                  t.Entry(False, t.Rel(1, 0), (1, 0))], ['close', 0, 1])

    failures = [
        lambda: t.axiom(t.Rel(4, 0)),                    # fifth free slot
        lambda: t.axiom(t.All(t.Rel(5, 0))),             # fifth free slot under binder
        lambda: t.axiom(['hole', 0, 1, 2, 3]),           # injected template marker
        lambda: t.axiom(['rel', True, 0]),               # bool is not natural syntax
        lambda: t.check_refutation({'matrices': [], 'proof': ['bottom', 0],
                                     'theorem': ['bot']}),
        lambda: t.check_refutation({'matrices': [], 'proof': ['bottom', 0]}),
        lambda: t.check_tree([t.Entry(False, t.BOT)], ['bottom', 0]),
        lambda: t.check_tree([t.Entry(False, t.All(t.BOT))],
                              ['all', 0, 0, ['bottom', 1]]),
        lambda: t.check_tree([t.Entry(True, t.All(t.BOT))],
                              ['all', 0, 2, ['bottom', 1]]),
        lambda: t.check_tree([t.Entry(True, t.Imp(t.BOT, t.BOT))],
                              ['imp', 0, ['bottom', 1]]),
        lambda: t.check_tree([t.Entry(True, t.Rel(0, 0), (0,)),
                              t.Entry(False, t.Rel(0, 0), (1,))], ['close', 0, 1]),
    ]
    for failure in failures:
        expect_reject(failure)
    for n in range(10000):
        assert t.encode_matrix(t.decode_matrix(n)) == n
        assert t.encode_tree(t.decode_tree(n)) == n
    for n in range(2000):
        assert not t.accepts_number(n)
    for matrix in forms:
        certificate = {'matrices': [matrix], 'proof': ['bottom', 0]}
        normalized = t.decode_certificate(t.encode_certificate(certificate))
        assert normalized['matrices'] == certificate['matrices']
        assert normalized['proof'] == certificate['proof']

    counts = Counter()
    unique = set()
    def walk(f):
        counts[f[0]] += 1
        unique.add(f)
        if f[0] == 'all': walk(f[1])
        if f[0] == 'imp': walk(f[1]); walk(f[2])
    walk(t.TEMPLATE)
    return {'status': 'passed', 'matrix_cases': len(forms),
            'direct_schema_semantic_cases': semantic_cases,
            'matrix_projection_semantic_cases': differential_cases,
            'virtual_expanded_identity_proof_cases': identity_cases,
            'invalid_certificate_rejections': len(failures),
            'matrix_code_roundtrips': 10000, 'proof_code_roundtrips': 10000,
            'finite_refutation_enumeration_control': 2000,
            'cross_variable_specialization_checked': True,
            'bottom_specialization_checked': True,
            'template_tree_nodes_with_holes': sum(counts.values()),
            'template_distinct_nodes_with_holes': len(unique),
            'template_constructors': dict(counts),
            'public_refutation_found': False,
            'logical_correctness_status': 'ordinary_math_argument_not_kernel_checked',
            'EPSC2_strength_status': 'separate_theory_argument',
            'literal_TM_or_state_bound_claimed': False}


if __name__ == '__main__':
    result = run()
    output = Path(__file__).with_name('epsc2_tableau_results.json')
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))
