#!/usr/bin/env python3
"""Finite integration checks for the two-map proof kernel and schema emitter.

These checks are evidence for the implementation; the general completeness
and calibration arguments are in the report. No finite run can prove that
the fixed consistency search never halts.
"""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path
import random
import time

import fixed_theory as theory
import fused_stream as stream
import name_transport as names
import proof_transport as proofs
import two_kernel as k
import unary_union as unary
from vendor import four_kernel as old
from vendor import stream_four


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def rejects(fn, *args):
    try:
        fn(*args)
    except (ValueError, TypeError, KeyError):
        return
    raise AssertionError('malformed or nonrefuting input was accepted')


def random_formula(rng, size, depth=0, free=(-2, -1, 0, 1, 2)):
    if size == 0:
        if rng.randrange(5) == 0:
            return k.BOT
        def var():
            return k.B(rng.randrange(depth)) if depth and rng.randrange(2) else k.F(rng.choice(free))
        return k.R(var(), var())
    choice = rng.randrange(3)
    if choice == 0:
        return k.All(random_formula(rng, size - 1, depth + 1, free))
    if choice == 1:
        return k.Imp(random_formula(rng, size - 1, depth, free),
                     random_formula(rng, size - 1, depth, free))
    return random_formula(rng, 0, depth, free)


def verify(output_dir):
    started = time.monotonic()
    rng = random.Random(2026101703)
    output_dir.mkdir(parents=True, exist_ok=True)
    evidence = {'status': 'PASS', 'scope': 'finite reference-code checks; no literal TM bound'}

    # Independent implementation of the same variable-output transducers.
    scanner_cases = 0
    formulas = [random_formula(rng, 4) for _ in range(200)]
    for x in range(-100, 101):
        formulas.append(k.All(k.R(k.F(x), k.B(0))))
    for formula in formulas:
        require(k.scoped(formula), 'test formula scope')
        for mode, op in [('u', 'up'), ('w', 'fused_down')]:
            bits = names.encode(formula)
            want = names.encode(k.rename_step(op, formula))
            require(stream.transduce(mode, bits) == want, 'root scanner mismatch')
            require(names.transduce(mode, bits) == want, 'independent scanner mismatch')
            scanner_cases += 1
    counts4 = {op: stream_four.table(op)['states'] for op in 'sStk'}
    counts3 = {op: stream.table(op)['states'] for op in ('s', 'S', 'g')}
    counts2 = {op: stream.table(op)['states'] for op in ('u', 'w')}
    require(sum(counts4.values()) == 46 and sum(counts2.values()) == 24, 'control inventory')
    evidence['whole_formula_stream_checks'] = scanner_cases
    evidence['stream_states'] = {'four': counts4, 'three': counts3, 'two': counts2}
    (output_dir/'stream_tables.json').write_text(json.dumps({
        'counting_convention': 'Sum of independent lexical stream-transducer controls; variable output; NOT one-tape TM states.',
        'four': {op: stream_four.table(op) for op in 'sStk'},
        'three': {op: stream.table(op) for op in ('s', 'S', 'g')},
        'two': {op: stream.table(op) for op in ('u', 'w')}}, indent=2) + '\n')

    # Collision-sensitive UI, including source19's prior regression case.
    old_ui = old.make_ui_certificate(old.source19_body(), 0)
    new_ui, audit = proofs.translate(old_ui)
    k.check_certificate(new_ui)
    back_ui = proofs.reverse_translate(new_ui)
    require(old.check_certificate(back_ui)[-1] == old.check_certificate(old_ui)[-1], 'reverse collision UI')
    (output_dir/'collision_ui_certificate.json').write_text(json.dumps(
        {'original': old_ui, 'translated': new_ui, 'audit': audit}, indent=2) + '\n')
    evidence['collision_ui'] = {name: audit[name] for name in ('old_lines', 'expanded_lines', 'new_lines')}
    evidence['collision_ui']['reverse_translated_lines'] = len(back_ui['instructions'])
    translation_cases = 1
    for _ in range(60):
        body = random_formula(rng, 3, depth=1)
        target = rng.randrange(-3, 4)
        certificate = old.make_ui_certificate(body, target)
        translated, _ = proofs.translate(certificate)
        require(k.check_certificate(translated)[-1] == old.Imp(old.All(body), old.open_body(body, target)), 'UI exact conclusion')
        reversed_certificate = proofs.reverse_translate(translated)
        require(old.check_certificate(reversed_certificate)[-1] == old.check_certificate(certificate)[-1], 'reverse exact conclusion')
        translation_cases += 1

    # Backreferences, all logical constructors, MP and generalization survive.
    a, b, c = k.R(k.F(0), k.F(1)), k.R(k.F(-2), k.F(2)), k.BOT
    instructions = [
        {'op': 'K', 'a': a, 'b': k.Imp(a, a)},
        {'op': 'K', 'a': a, 'b': a},
        {'op': 'S', 'a': a, 'b': k.Imp(a, a), 'c': a},
        {'op': 'mp', 'implication': 2, 'antecedent': 0},
        {'op': 'mp', 'implication': 3, 'antecedent': 1},
        {'op': 'Peirce', 'a': a, 'b': b},
        {'op': 'exfalso', 'a': a},
        {'op': 'distribution', 'a': k.R(k.B(0), k.F(0)), 'b': k.BOT},
        {'op': 'vacuity', 'a': a},
        {'op': 'fresh_ui', 'body': k.R(k.B(0), k.F(1)), 'fresh': 0},
        {'op': 'axiom', 'index': 0}]
    for _ in range(40):
        instructions.append({'op': rng.choice(['up', 'down', 'swap', 'contract']),
                             'line': rng.randrange(len(instructions))})
        instructions.append({'op': 'gen', 'line': len(instructions) - 1,
                             'name': rng.randrange(-2, 3)})
    instructions.append({'op': 'swap', 'line': 10})  # closed CP; final alias/truncation
    translated, mixed_audit = proofs.translate({'instructions': instructions}, [theory.CP])
    require(k.check_certificate(translated, [theory.CP])[-1] == theory.CP, 'closed final alias')
    evidence['proof_translation_cases'] = translation_cases + 1
    evidence['reverse_translation_cases'] = translation_cases
    evidence['mixed_proof'] = {name: mixed_audit[name] for name in ('old_lines', 'expanded_lines', 'new_lines')}

    # New materialization of the prior unary+BU schema against direct semantics.
    matrices = [k.BOT, k.Imp(k.BOT, k.BOT)] + [
        random_formula(rng, 2, free=(0, 1, 2)) for _ in range(14)]
    semantic_cases = 0
    all_axioms = [theory.CP]
    for matrix in matrices:
        wrapped = unary.axiom(matrix)
        all_axioms += [wrapped, theory.gic_axiom(matrix)]
        for n in (1, 2):
            domain = tuple(range(n))
            for mask in range(1 << (n*n)):
                relation = lambda x, y, mask=mask, n=n: bool(mask & (1 << (x*n+y)))
                require(k.evaluate(wrapped, domain, relation, lambda _: 0)
                        == unary.direct(matrix, domain, relation), 'unary wrapper semantics')
                semantic_cases += 1
    for axiom in all_axioms:
        require(k.scoped(axiom) and not k.free_names(axiom), 'axiom not closed')
        for op in k.RENAMINGS:
            require(k.rename_step(op, axiom) == axiom, 'closed axiom changed')
    evidence['unary_schema_semantic_cases'] = semantic_cases
    evidence['closed_axioms_checked'] = len(all_axioms)
    (output_dir/'unary_false_instance.json').write_text(json.dumps(unary.axiom(k.BOT), indent=2) + '\n')

    # These fixed theory entries cannot be turned into arbitrary-theory search.
    rejects(k.check_certificate, {'instructions': [{'op': 'axiom', 'index': 0}]}, [a])
    rejects(k.check_certificate, {'instructions': [{'op': 'fresh_ui', 'body': k.R(k.B(0), k.F(0)), 'fresh': 0}]})
    rejects(k.check_certificate, {'instructions': [{'op': 'up', 'line': 0}]})
    for removed in ('down', 'swap', 'contract'):
        rejects(k.check_certificate, {'instructions': [{'op': 'K', 'a': a, 'b': b}, {'op': removed, 'line': 0}]})
    for checker in (theory.check_refutation, unary.check_refutation):
        rejects(checker, {'matrices': [], 'proof': []})
        rejects(checker, {'matrices': [], 'proof': [], 'target': k.BOT})
        rejects(checker, {'matrices': [], 'proof': [], 'theory': [k.BOT]})
        rejects(checker, {'matrices': [], 'proof': [{'op': 'K', 'a': a, 'b': b}]})
    rejects(unary.axiom, k.R(k.F(3), k.F(0)))
    rejects(unary.axiom, k.R(k.B(0), k.F(0)))
    for data in (b'', b'null', b'NaN', b'[]', b'{"matrices": [], "proof": []}', b'\xff'):
        require(not theory.accepts_bytes(data), 'nonrefuting bytes accepted')
        require(not unary.accepts_bytes(data), 'nonrefuting unary bytes accepted')
    for data in (b'', b'\x00', b'\xff', b'hello', bytes(range(256))):
        require(theory.shortlex_bytes_at(theory.index_of_bytes(data)) == data, 'shortlex roundtrip')
    evidence['negative_interface_checks'] = 28
    evidence['shortlex_roundtrips'] = 5
    evidence['elapsed_seconds'] = round(time.monotonic() - started, 6)
    (output_dir/'integration_results.json').write_text(json.dumps(evidence, indent=2) + '\n')
    return evidence


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=Path(__file__).resolve().parents[1]/'data')
    arguments = parser.parse_args()
    print(json.dumps(verify(arguments.output_dir), indent=2))
