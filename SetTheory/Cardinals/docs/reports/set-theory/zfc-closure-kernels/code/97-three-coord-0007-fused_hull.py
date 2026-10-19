#!/usr/bin/env python3
"""Fuse H with N, optionally encoding G(b,t) as Eq(A(b,t),d).

The product-model proof in selective_equality.tex justifies these exact source
changes. Both versions have eight proper functions and use a total radix-eight
ground term codec with two explicit constants. Neither is a binary TM.
"""
from __future__ import annotations
import itertools
import json
from pathlib import Path

import selective_equality as S

HERE = Path(__file__).resolve().parent
FUNCTIONS = [(name, arity) for name, arity in S.FUNCTIONS if name != 'H']
TAGS = {name: i for i, (name, _) in enumerate(FUNCTIONS)}


def rename_hull(t):
    if isinstance(t, str):
        return t
    return ('N' if t[0] == 'H' else t[0],) + tuple(rename_hull(u) for u in t[1:])


def source(extensional=False, coded_guard=False):
    rows = []
    for row in S.clauses(extensional):
        out = []
        for sign, pred, a, b in row:
            a, b = rename_hull(a), rename_hull(b)
            if coded_guard and pred == 'G':
                pred, a, b = 'Eq', S.K.f('A', a, b), S.K.d
            out.append((sign, pred, a, b))
        rows.append(out)
    return rows


def encode_number(tree):
    if tree in S.CONSTANTS:
        return S.CONSTANTS.index(tree)
    return 2 + TAGS[tree[0]] + 8 * S.K.tuple_code([encode_number(t) for t in tree[1:]])


def decode_number(n):
    if n < 2:
        return S.CONSTANTS[n]
    tag, body = (n - 2) % 8, (n - 2) // 8
    name, arity = FUNCTIONS[tag]
    args = S.K.tuple_decode(body, arity)
    assert all(a < n for a in args)
    return (name,) + tuple(decode_number(a) for a in args)


def ground_term(tree, env):
    if isinstance(tree, str):
        return env[tree]
    if tree in S.CONSTANTS:
        return S.CONSTANTS.index(tree)
    return 2 + TAGS[tree[0]] + 8 * S.K.tuple_code([ground_term(t, env) for t in tree[1:]])


def ground(rows, n):
    for row in rows:
        variables = S.K.clause_variables(row)
        for values in itertools.product(range(n + 1), repeat=len(variables)):
            env = dict(zip(variables, values))
            yield tuple((1 if sign else -1) * (1 + S.K.atom_code(
                pred, ground_term(a, env), ground_term(b, env)))
                for sign, pred, a, b in row)


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    report = {'scope': 'Product-model constructor fusion and exact finite inputs; no TM state count',
              'proper_functions': FUNCTIONS, 'ground_radix': 8,
              'padding_constructors': 0, 'constants': ['d', 'q'], 'variants': {}}
    for n in range(4096):
        assert encode_number(decode_number(n)) == n
    for extensional in (False, True):
        for guard in (False, True):
            name = ('se20n' if extensional else 'se19n') + ('_guard' if guard else '')
            rows = source(extensional, guard)
            predicates = ['E', 'Inc', 'Eq'] if guard else S.PREDICATES
            bits = S.encode_payload(rows, True, FUNCTIONS, predicates)
            assert S.decode_payload(bits, True, FUNCTIONS, predicates) == S.X._canonical(rows)
            for bad in (bits[:-1], bits + '0'):
                try:
                    S.decode_payload(bad, True, FUNCTIONS, predicates)
                except ValueError:
                    pass
                else:
                    raise AssertionError('Accepted malformed stream')
            (output / (name + '.json')).write_text(json.dumps(rows, indent=2) + '\n')
            (output / (name + '.bits')).write_text(bits + '\n')
            padded = bits + '0' * (-len(bits) % 8)
            (output / (name + '.bin')).write_bytes(int(padded, 2).to_bytes(len(padded) // 8, 'big'))
            data = S.metrics(rows, True, FUNCTIONS, predicates)
            assert data['proper_functions'] == 8
            assert data['payload_bits'] == (1138 if extensional else 971) + (48 if guard else 0)
            data['stages'] = []
            for stage in (0, 1):
                cnf = list(ground(rows, stage))
                witness = S.K.solve(cnf)
                assert witness is not None and S.K.valuation_satisfies(cnf, witness)
                data['stages'].append({'stage': stage, 'status': 'SAT',
                    'ground_instances': len(cnf),
                    'atoms': len({abs(l) for r in cnf for l in r}),
                    'maximum_atom_code_bits': max(abs(l).bit_length() for r in cnf for l in r),
                    'checked_witness_literals': len(witness),
                    'scope': 'Finite ground-CNF SAT witness only'})
            report['variants'][name] = data
    report['checks'] = {'numeric_term_roundtrips': 4096,
                        'exact_payload_roundtrips': 4,
                        'malformed_stream_rejections': 8,
                        'checked_finite_sat_witnesses': 8}
    (output / 'fused_results.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    print(json.dumps(run(HERE / 'results'), indent=2))
