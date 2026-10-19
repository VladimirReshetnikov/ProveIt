#!/usr/bin/env python3
"""Emit the selective-equality FC19/FC20 theories and their fair refuter.

This is an exact finite-formalism/reference-code contribution, not a binary TM
compiler.  The theorem in selective_equality.tex proves the ZFC consistency
calibration using a formula-by-formula interpretation on the Eq quotient.
The native source44 clauses are retained, except that the selector q becomes
an independently charged constant.  The four added universal clauses are:
left-Euclidean Eq, assignment-argument V transport, E transport, and d != q.
No other function or predicate transport is silently imposed.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE / 'reference'
sys.path.insert(0, str(REFERENCE))
import ground_kernel as K
import coded_extensional as X
sys.path.pop(0)

FUNCTIONS = K.signature(False, True)
CONSTANTS = [('d',), ('q',)]
PREDICATES = K.PREDICATES
Q = ('q',)


def named_selector(term):
    if term == K.q:
        return Q
    if isinstance(term, str):
        return term
    return (term[0],) + tuple(named_selector(x) for x in term[1:])


def native_clauses(extensional=False, named=True):
    rows = X.native_clauses() if extensional else K.source_clauses(False, True)
    if named:
        rows = [[(s, p, named_selector(a), named_selector(b)) for s, p, a, b in row]
                for row in rows]
    return rows


def completion(named=True):
    q = Q if named else K.q
    return [
        [K.Eq('x', 'y', False), K.Eq('x', 'z', False), K.Eq('y', 'z')],
        [K.Eq('s', 't', False),
         K.Eq(K.f('V', 's', 'j'), K.f('V', 't', 'j'))],
        [K.Eq('a', 'b', False), K.Eq('x', 'y', False),
         K.E('a', 'x', False), K.E('b', 'y')],
        [K.Eq(K.d, q, False)],
    ]


def clauses(extensional=False, named=True):
    return native_clauses(extensional, named) + completion(named)


def encode_payload(rows, named=True, functions=FUNCTIONS, predicates=PREDICATES):
    constants = CONSTANTS if named else CONSTANTS[:1]
    function_tag = {name: 4 + len(constants) + i for i, (name, _) in enumerate(functions)}
    assert 4 + len(constants) + len(functions) <= 16
    pieces = []
    for row in rows:
        names = {name: i for i, name in enumerate(K.clause_variables(row))}
        assert len(names) <= 4 and 0 < len(row) < 8

        def term(t):
            if isinstance(t, str):
                return format(names[t], '04b')
            if t in constants:
                return format(4 + constants.index(t), '04b')
            return format(function_tag[t[0]], '04b') + ''.join(term(u) for u in t[1:])

        pieces.append(format(len(row), '03b'))
        for sign, pred, a, b in row:
            pieces.extend((str(int(sign)), format(predicates.index(pred), '02b'), term(a), term(b)))
    return ''.join(pieces) + '000'


def decode_payload(bits, named=True, functions=FUNCTIONS, predicates=PREDICATES):
    """Independent cursor parser; no term/row input from the encoder is used."""
    constants = CONSTANTS if named else CONSTANTS[:1]
    signature = [(c[0], 0) for c in constants] + functions
    position = 0

    def read(width):
        nonlocal position
        if position + width > len(bits):
            raise ValueError('truncated stream')
        token = bits[position:position + width]
        position += width
        if any(bit not in '01' for bit in token):
            raise ValueError('nonbinary stream')
        return int(token, 2)

    def term():
        tag = read(4)
        if tag < 4:
            return 'v' + str(tag)
        if tag - 4 >= len(signature):
            raise ValueError('unassigned term opcode')
        name, arity = signature[tag - 4]
        return (name,) + tuple(term() for _ in range(arity))

    rows = []
    while True:
        size = read(3)
        if size == 0:
            if position != len(bits):
                raise ValueError('trailing bits')
            return rows
        row = []
        for _ in range(size):
            sign, predicate_code = bool(read(1)), read(2)
            if predicate_code >= len(predicates):
                raise ValueError('unassigned predicate opcode')
            predicate = predicates[predicate_code]
            row.append((sign, predicate, term(), term()))
        rows.append(row)


def metrics(rows, named=True, functions=FUNCTIONS, predicates=PREDICATES):
    bits = encode_payload(rows, named, functions, predicates)
    return {
        'clauses': len(rows),
        'literals': sum(map(len, rows)),
        'term_nodes': sum(K.term_nodes(t) for row in rows for literal in row for t in literal[2:]),
        'maximum_variables': max(map(lambda row: len(K.clause_variables(row)), rows)),
        'maximum_term_depth': max(K.term_depth(t) for row in rows for literal in row for t in literal[2:]),
        'constants': 2 if named else 1,
        'proper_functions': len(functions),
        'predicate_symbols_including_Eq': len(predicates),
        'term_opcode_bits': 4,
        'payload_bits': len(bits),
        'payload_sha256': hashlib.sha256(bits.encode()).hexdigest(),
        'ground_instance_polynomial_by_degree': dict(sorted(Counter(
            len(K.clause_variables(row)) for row in rows).items())),
        'packed_bytes': (len(bits) + 7) // 8,
        'padding_bits': -len(bits) % 8,
    }


def decode_number(number):
    """Bijection N -> terms: d=0, q=1, 16 proper/padding constructor tags."""
    if number < 2:
        return CONSTANTS[number]
    tag, body = (number - 2) % 16, (number - 2) // 16
    name, arity = FUNCTIONS[tag] if tag < len(FUNCTIONS) else ('junk' + str(tag), 1)
    children = K.tuple_decode(body, arity)
    assert all(child < number for child in children)
    return (name,) + tuple(decode_number(x) for x in children)


def encode_number(tree):
    if tree in CONSTANTS:
        return CONSTANTS.index(tree)
    tags = {name: i for i, (name, _) in enumerate(FUNCTIONS)}
    tag = tags[tree[0]] if tree[0] in tags else int(tree[0][4:])
    return 2 + tag + 16 * K.tuple_code([encode_number(t) for t in tree[1:]])


def ground_term(tree, environment):
    if isinstance(tree, str):
        return environment[tree]
    if tree in CONSTANTS:
        return CONSTANTS.index(tree)
    tags = {name: i for i, (name, _) in enumerate(FUNCTIONS)}
    return 2 + tags[tree[0]] + 16 * K.tuple_code([ground_term(t, environment) for t in tree[1:]])


def ground_rows(rows, frontier):
    for row in rows:
        variables = K.clause_variables(row)
        for values in itertools.product(frontier, repeat=len(variables)):
            environment = dict(zip(variables, values))
            yield tuple((1 if sign else -1) * (1 + K.atom_code(
                predicate, ground_term(a, environment), ground_term(b, environment)))
                for sign, predicate, a, b in row)


def decide_stage(n, extensional=False):
    """Decide exactly all substitutions 0..n into the finite universal list.

    Endpoint terms are retained even when their codes exceed n.  No built-in
    equality or congruence is added by the SAT solver: Eq is an ordinary atom.
    Resource errors propagate.  They are never interpreted as inconsistency.
    """
    cnf = list(ground_rows(clauses(extensional), range(n + 1)))
    witness = K.solve(cnf)
    assert witness is None or K.valuation_satisfies(cnf, witness)
    return {
        'stage': n,
        'status': 'UNSAT' if witness is None else 'SAT',
        'ground_instances': len(cnf),
        'distinct_atoms': len({abs(lit) for row in cnf for lit in row}),
        'maximum_atom_code_bits': max(abs(lit).bit_length() for row in cnf for lit in row),
        'checked_witness_literals': 0 if witness is None else len(witness),
        'scope': 'One finite ground CNF; SAT is not consistency or a finite model of the whole theory',
    }


def whole_search(extensional=False):
    for n in itertools.count():
        result = decide_stage(n, extensional)
        if result['status'] == 'UNSAT':
            return result


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    result = {'scope': 'Exact finite-theory reduction and reference refuter; no binary TM/state claim',
              'theories': {}, 'references': {}, 'prior_reduct_controls': {}}
    for name in ('ground_kernel.py', 'coded_extensional.py', 'finite_class_closure.md', 'LICENSE.ProveIt'):
        result['references'][name] = hashlib.sha256((REFERENCE / name).read_bytes()).hexdigest()
    prior_completion = K.equality_clauses(False, [('V', 2), ('C', 3)])[1:-1]
    for extensional, name, expected_bits in [(False, 'fc15_prior', 1134), (True, 'fc16_prior', 1341)]:
        prior = native_clauses(extensional, False) + prior_completion
        control = K.metrics(prior, functions=FUNCTIONS)
        control['ground_instance_polynomial_by_degree'] = dict(sorted(Counter(
            len(K.clause_variables(row)) for row in prior).items()))
        assert control['template_bits'] == expected_bits
        result['prior_reduct_controls'][name] = control
    malformed = 0
    for extensional in (False, True):
        for named in (False, True):
            name = ('fc20' if extensional else 'fc19') + ('_named' if named else '_one_constant')
            rows = clauses(extensional, named)
            bits = encode_payload(rows, named)
            assert decode_payload(bits, named) == X._canonical(rows)
            for bad in (bits[:-1], bits + '0', bits[:17]):
                try:
                    decode_payload(bad, named)
                except ValueError:
                    malformed += 1
                else:
                    raise AssertionError('Malformed payload was accepted')
            (output / (name + '.json')).write_text(json.dumps(rows, indent=2) + '\n')
            (output / (name + '.bits')).write_text(bits + '\n')
            padded = bits + '0' * (-len(bits) % 8)
            (output / (name + '.bin')).write_bytes(int(padded, 2).to_bytes(len(padded) // 8, 'big'))
            result['theories'][name] = metrics(rows, named)
    assert result['theories']['fc19_named']['clauses'] == 19
    assert result['theories']['fc19_named']['literals'] == 45
    assert result['theories']['fc20_named']['clauses'] == 20
    assert result['theories']['fc20_named']['literals'] == 49
    for number in range(4096):
        assert encode_number(decode_number(number)) == number
    # Independent substitution-by-tree decoding, versus direct code arithmetic.
    ground_checks = 0
    for extensional in (False, True):
        for row in clauses(extensional):
            vs = K.clause_variables(row)
            for values in itertools.product(range(3), repeat=len(vs)):
                env = dict(zip(vs, values))

                def substitute(t):
                    if isinstance(t, str):
                        return decode_number(env[t])
                    return (t[0],) + tuple(substitute(u) for u in t[1:])

                for _, _, a, b in row:
                    for t in (a, b):
                        assert ground_term(t, env) == encode_number(substitute(t))
                        ground_checks += 1
    # Exact SAT controls ensure the raw-predicate interpretation isn't augmented
    # by an unintended general equality decision procedure.
    local = {
        'Inc_assignment_may_split_Eq': [[1], [2], [-3]],
        'Inc_class_may_split_Eq': [[1], [2], [-3]],
    }
    # Here atoms are just three independent propositions: Eq(a,b), Inc(a,c),
    # Inc(b,c) (or Eq(a,b), Inc(c,a), Inc(c,b)). This is a local clause control.
    for cnf in local.values():
        witness = K.solve(cnf)
        assert witness is not None and K.valuation_satisfies(cnf, witness)
    rng = random.Random(191945)
    sat_comparisons = 0
    for _ in range(200):
        cnf = [[rng.choice((-1, 1)) * rng.randrange(1, 7)
                for _ in range(rng.randrange(1, 5))]
               for _ in range(rng.randrange(0, 13))]
        got = K.solve(cnf)
        expected = K.exhaustive_sat(cnf)
        assert (got is None) == (expected is None)
        assert got is None or K.valuation_satisfies(cnf, got)
        sat_comparisons += 1
    result['checks'] = {
        'exact_payload_roundtrips': 4,
        'malformed_payload_rejections': malformed,
        'numeric_codec_roundtrips': 4096,
        'independent_ground_endpoint_comparisons': ground_checks,
        'small_cnf_exhaustive_comparisons': sat_comparisons,
        'local_raw_Inc_controls': len(local),
    }
    result['stages'] = {name: [decide_stage(n, ext) for n in (0, 1)]
                        for name, ext in [('fc19_named', False), ('fc20_named', True)]}
    (output / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE / 'results')
    parser.add_argument('--stage', type=int)
    parser.add_argument('--whole-search', action='store_true')
    parser.add_argument('--extensional', action='store_true')
    args = parser.parse_args()
    if args.whole_search:
        result = whole_search(args.extensional)
    elif args.stage is not None:
        assert args.stage >= 0
        result = decide_stage(args.stage, args.extensional)
    else:
        result = run(args.output)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
