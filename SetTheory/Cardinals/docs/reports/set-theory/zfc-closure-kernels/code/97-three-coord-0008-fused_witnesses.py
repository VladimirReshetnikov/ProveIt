#!/usr/bin/env python3
"""Exact six- and five-function selective-equality presentations.

H is replaced by N. Y(b,t,u)=A(C(b,t,u),d) and
Z(b,t,u)=Q(C(b,t,u),d). The five-function version additionally has
W(s,j,a)=A(C(s,j,a),q). See the injective-raw-update product model
in selective_equality.tex. No injectivity axiom is added to the input.
These are finite-formalism payloads and a reference refuter, not binary TMs.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

import selective_equality as S

HERE = Path(__file__).resolve().parent


def signature(share_witness):
    removed = {'H', 'Y', 'Z'} | ({'W'} if share_witness else set())
    return [(name, arity) for name, arity in S.FUNCTIONS if name not in removed]


def transform(tree, share_witness):
    if isinstance(tree, str):
        return tree
    name, *children = tree
    children = tuple(transform(t, share_witness) for t in children)
    if name == 'H':
        return ('N',) + children
    if name in ('Y', 'Z'):
        return ('A' if name == 'Y' else 'Q', ('C',) + children, S.K.d)
    if name == 'W' and share_witness:
        return ('A', ('C',) + children, S.Q)
    return (name,) + children


def source(extensional=False, share_witness=False):
    return [[(sign, pred, transform(a, share_witness), transform(b, share_witness))
             for sign, pred, a, b in row] for row in S.clauses(extensional)]


def encode_number(tree, functions):
    if tree in S.CONSTANTS:
        return S.CONSTANTS.index(tree)
    tags = {name: i for i, (name, _) in enumerate(functions)}
    tag = tags[tree[0]] if tree[0] in tags else int(tree[0][4:])
    return 2 + tag + 8 * S.K.tuple_code([encode_number(t, functions) for t in tree[1:]])


def decode_number(number, functions):
    if number < 2:
        return S.CONSTANTS[number]
    tag, body = (number - 2) % 8, (number - 2) // 8
    name, arity = functions[tag] if tag < len(functions) else ('junk' + str(tag), 1)
    children = S.K.tuple_decode(body, arity)
    assert all(child < number for child in children)
    return (name,) + tuple(decode_number(child, functions) for child in children)


def ground_term(tree, environment, functions):
    if isinstance(tree, str):
        return environment[tree]
    if tree in S.CONSTANTS:
        return S.CONSTANTS.index(tree)
    tags = {name: i for i, (name, _) in enumerate(functions)}
    return 2 + tags[tree[0]] + 8 * S.K.tuple_code([
        ground_term(child, environment, functions) for child in tree[1:]])


def ground(rows, stage, functions):
    for row in rows:
        variables = S.K.clause_variables(row)
        for values in itertools.product(range(stage + 1), repeat=len(variables)):
            environment = dict(zip(variables, values))
            yield tuple((1 if sign else -1) * (1 + S.K.atom_code(
                pred, ground_term(a, environment, functions),
                ground_term(b, environment, functions))) for sign, pred, a, b in row)


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    report = {'scope': 'Injective-model witness sharing and exact finite inputs; no TM state count',
              'ground_radix': 8, 'constants': ['d', 'q'], 'variants': {}}
    roundtrips = 0
    for share in (False, True):
        functions = signature(share)
        for number in range(4096):
            assert encode_number(decode_number(number, functions), functions) == number
            roundtrips += 1
        for extensional in (False, True):
            name = ('se20n' if extensional else 'se19n') + ('5' if share else '6')
            rows = source(extensional, share)
            bits = S.encode_payload(rows, True, functions)
            assert S.decode_payload(bits, True, functions) == S.X._canonical(rows)
            for malformed in (bits[:-1], bits + '0'):
                try:
                    S.decode_payload(malformed, True, functions)
                except ValueError:
                    pass
                else:
                    raise AssertionError('Accepted malformed stream')
            (output / (name + '.json')).write_text(json.dumps(rows, indent=2) + '\n')
            (output / (name + '.bits')).write_text(bits + '\n')
            padded = bits + '0' * (-len(bits) % 8)
            (output / (name + '.bin')).write_bytes(int(padded, 2).to_bytes(len(padded) // 8, 'big'))
            data = S.metrics(rows, True, functions)
            data['signature'] = functions
            data['ground_radix'] = 8
            data['padding_constructors'] = 8 - len(functions)
            assert data['proper_functions'] == (5 if share else 6)
            assert data['payload_bits'] == (1138 if extensional else 971) + 40 + (16 if share else 0)
            assert data['term_nodes'] == (232 if extensional else 194) + 10 + (4 if share else 0)
            data['stages'] = []
            for stage in (0, 1):
                cnf = list(ground(rows, stage, functions))
                witness = S.K.solve(cnf)
                assert witness is not None and S.K.valuation_satisfies(cnf, witness)
                data['stages'].append({'stage': stage, 'status': 'SAT',
                    'ground_instances': len(cnf),
                    'atoms': len({abs(literal) for row in cnf for literal in row}),
                    'maximum_atom_code_bits': max(abs(literal).bit_length()
                                                  for row in cnf for literal in row),
                    'checked_witness_literals': len(witness),
                    'scope': 'Finite ground-CNF SAT witness only'})
            report['variants'][name] = data
    report['checks'] = {'numeric_term_roundtrips': roundtrips,
                        'exact_payload_roundtrips': 4,
                        'malformed_stream_rejections': 8,
                        'checked_finite_sat_witnesses': 8}
    (output / 'fused_witness_results.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    print(json.dumps(run(HERE / 'results'), indent=2))
