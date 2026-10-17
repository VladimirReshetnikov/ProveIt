#!/usr/bin/env python3
"""Independent finite audit of EPSC2 default-index normalization.

These tests compare a changed running checker with the separately retained
original. Logical identity certificates are never submitted as PSC refutations.
Finite tests are evidence for implementation, not a consistency proof.
"""
from __future__ import annotations

from itertools import product
import hashlib
import json
from pathlib import Path

import epsc2_original as old
import epsc2_default_indices as new


def canonical(formula, width):
    """Independent recursive normalization, expressed by a local name map."""
    names = tuple(range(width))
    def atom_index(i):
        try:
            return names[i]
        except IndexError:
            return names[-1]
    tag = formula[0]
    if tag == 'bot':
        return old.BOT
    if tag == 'rel':
        return old.Rel(atom_index(formula[1]), atom_index(formula[2]))
    if tag == 'all':
        return old.All(canonical(formula[1], width + 1))
    return old.Imp(canonical(formula[1], width), canonical(formula[2], width))


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
    return all(evaluate(e.child(e.formula[1], environment=(v,) + e.environment),
                        relation, size) for v in range(size))


def identity(entry, positive=0, negative=1, length=2, fresh=1):
    """Produce A, not-A demonstrations; acceptance is checked independently."""
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


def accepts(module, certificate):
    try:
        return bool(module.check_refutation(certificate)['valid'])
    except ValueError:
        return False


def expect_reject(call):
    try:
        call()
    except ValueError:
        return
    raise AssertionError('An invalid public input was accepted')


def run():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    decoder_cases = semantic_cases = identity_cases = wrapper_cases = 0
    for width in range(1, 9):
        for code in range(10000):
            raw = old.decode_matrix(code)
            normal = canonical(raw, width)
            assert new.normalize(raw, width) == normal
            assert old.scoped(normal, width)
            assert canonical(normal, width) == normal
            if old.scoped(raw, width):
                assert normal == raw
            # A canonical valid code is fixed by the total interpretation.
            assert canonical(old.decode_matrix(old.encode_matrix(normal)), width) == normal
            decoder_cases += 1

    # Large raw payloads, capture-sensitive depth changes, and ordinary formulas.
    forms = [old.decode_matrix(i) for i in range(120)]
    forms += [old.Rel(4, 10000), old.All(old.Rel(4, 99999)),
              old.All(old.All(old.Rel(5, 1000))),
              old.Imp(old.Rel(999, 0), old.All(old.Rel(5, 1)))]
    for raw in forms:
        normal = canonical(raw, 4)
        for env in product(range(2), repeat=4):
            for relation in range(16):
                a = evaluate(new.Entry(True, raw, env), relation, 2)
                b = evaluate(old.Entry(True, normal, env), relation, 2)
                assert a == b
                semantic_cases += 1
        # Actual fixed-template traversal and actual accepted logical trees.
        fresh_root = new.axiom(raw)
        proof = identity(fresh_root)
        fresh_result = new.check_tree(
            [fresh_root, new.Entry(False, new.TEMPLATE, (), raw)], proof)
        old_result = old.check_tree(
            [old.axiom(normal), old.Entry(False, old.TEMPLATE, (), normal)], proof)
        assert fresh_result == old_result
        identity_cases += 1
        for size in (1, 2):
            for relation in range(1 << (size * size)):
                assert evaluate(fresh_root, relation, size) == evaluate(
                    old.axiom(normal), relation, size)
                wrapper_cases += 1

    # Each projection is checked with arbitrary parent names. Normalization
    # must occur AFTER the fixed four-slot projection, at matrix-local scope.
    projection_cases = 0
    for raw in forms:
        normal = canonical(raw, 4)
        for env in product(range(2), repeat=5):
            for projection in ((2, 0, 4, 3), (1, 0, 4, 3), (0, 1, 4, 3)):
                a = new.Entry(True, new.Hole(*projection), env, raw)
                b = old.Entry(True, old.Hole(*projection), env, normal)
                for relation in (0, 1, 6, 9, 15):
                    assert evaluate(a, relation, 2) == evaluate(b, relation, 2)
                    projection_cases += 1

    # A fixed root-width clamp is wrong below a binder.
    raw = old.All(old.Rel(4, 9))
    correct = canonical(raw, 4)
    static_wrong = old.All(old.Rel(3, 3))
    env = (0, 0, 0, 1)
    relation = 1 << 3  # only R(1,1) is true
    assert correct == old.All(old.Rel(4, 4))
    assert evaluate(old.Entry(True, correct, env), relation, 2)
    assert not evaluate(old.Entry(True, static_wrong, env), relation, 2)

    # Clamping directly in the wrapper environment is also wrong. At this
    # actual SB projection, matrix slot3 is parent slot3, not parent slot4.
    raw = old.Rel(4, 4)
    parent = (0, 0, 0, 0, 1)
    projection = (2, 0, 4, 3)
    projected = tuple(parent[i] for i in projection)
    intended_atom = new.Entry(True, raw, projected).atom()
    premature_atom = new.Entry(True, raw, parent).atom()
    assert intended_atom == (0, 0) and premature_atom == (1, 1)

    # Cross-variable specialization continues to require the full tableau.
    transport = old.All(old.All(old.Imp(old.All(old.Rel(0, 2)), old.Rel(0, 1))))
    transport_proof = ['all', 0, ['all', 1, ['imp', 2,
                       ['all', 3, 2, ['close', 5, 4]]]]]
    assert old.check_tree([old.Entry(False, transport)], transport_proof) == \
           new.check_tree([new.Entry(False, transport)], transport_proof)

    # Public theory boundary: each decoded raw matrix is normalized only in
    # the independent comparison; same proof tree must have the same outcome.
    public_cases = accepted_public = newly_admissible = 0
    for code in range(10000):
        certificate = new.decode_certificate(code)
        expected = {'matrices': [canonical(m, 4) for m in certificate['matrices']],
                    'proof': certificate['proof']}
        a, b = accepts(new, certificate), accepts(old, expected)
        assert a == b
        accepted_public += a
        newly_admissible += any(not old.scoped(m, 4) for m in certificate['matrices'])
        public_cases += 1
    # Low outer codes do not yet reach many raw matrix payloads because of
    # nested pairing. Deliberately encode high-index matrices as full numeric
    # candidates, then run the actual numeric decoder and public checker.
    targeted_codec_cases = targeted_unscoped_cases = 0
    for raw in forms:
        certificate = {'matrices': [raw], 'proof': ['bottom', 0]}
        code = old.encode_certificate(certificate)
        decoded = new.decode_certificate(code)
        assert decoded == certificate
        expected = {'matrices': [canonical(raw, 4)], 'proof': certificate['proof']}
        assert accepts(new, decoded) == accepts(old, expected)
        targeted_unscoped_cases += not old.scoped(raw, 4)
        targeted_codec_cases += 1
    assert targeted_unscoped_cases > 0
    # This observed zero is a finite diagnostic, not a consistency argument.
    assert accepted_public == 0
    expect_reject(lambda: new.check_refutation(
        {'matrices': [], 'proof': ['bottom', 0], 'target': ['bot']}))
    expect_reject(lambda: new.check_refutation(
        {'matrices': [['rel', -1, 0]], 'proof': ['bottom', 0]}))
    expect_reject(lambda: new.check_refutation(
        {'matrices': [['all']], 'proof': ['bottom', 0]}))
    expect_reject(lambda: new.check_refutation(
        {'matrices': [['bot']], 'proof': ['bottom', 0]}))

    result = {
        'status': 'PASS',
        'decoder_and_retraction_cases': decoder_cases,
        'matrix_semantic_comparisons': semantic_cases,
        'accepted_logical_identity_certificates': identity_cases,
        'fixed_wrapper_semantic_comparisons': wrapper_cases,
        'matrix_projection_semantic_comparisons': projection_cases,
        'public_numeric_candidate_comparisons': public_cases,
        'numeric_candidates_with_formerly_out_of_scope_matrices': newly_admissible,
        'targeted_numeric_codec_cases': targeted_codec_cases,
        'targeted_formerly_out_of_scope_matrices': targeted_unscoped_cases,
        'accepted_public_refutations_in_tested_prefix': accepted_public,
        'negative_controls': {
            'fixed_depth_clamping_under_binder': 'fails as expected',
            'clamping_before_matrix_projection': 'fails as expected',
            'public_boundary_adversarial_cases': 4,
            'full_cross_variable_transport': 'retained and accepted',
        },
        'compiled_binary_state_count': None,
        'proof_assistant_verification': False,
        'claim': 'finite evidence for ordinary retraction and checker transport theorems',
        'sources': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                    for name in ['epsc2_original.py', 'epsc2_default_indices.py']},
    }
    destination = Path(__file__).with_name('default_indices_results.json')
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    run()
