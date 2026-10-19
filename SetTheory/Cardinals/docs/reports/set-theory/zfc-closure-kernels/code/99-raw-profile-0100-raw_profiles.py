#!/usr/bin/env python3
"""Exact payloads for a direct raw-profile interpretation of the FC15 kernel.

This is a clause generator and exact finite refuter, not a binary TM compiler.
The semantic proof is in raw_profiles.tex. No SAT verdict is inferred from a
resource limit. The retained source44 generator is copied in reference/.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from math import isqrt
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'reference'))
import ground_kernel as g
import coded_extensional as ce

PREDICATES = ['E', 'Inc', 'G', 'Eq']
CONSTANTS = ['d', 'q']
FUNCTIONS = g.signature(False, False)


def replace_selectors(t):
    """The new q is an independent constant constrained only by d != q."""
    if t == g.q:
        return ('q',)
    if isinstance(t, str):
        return t
    return (t[0],) + tuple(replace_selectors(a) for a in t[1:])


def native(extensional=False, fused_member=False, evaluation_member=False):
    if fused_member and evaluation_member:
        raise ValueError('choose only one member-selector fusion')
    rows = g.source_clauses(False, False)
    if extensional:
        rows += [ce.extensional_clause()]
    rows = [[(s, p, replace_selectors(a), replace_selectors(b))
             for s, p, a, b in row] for row in rows]
    if fused_member:
        # Z is constrained as a bad member only when G is false. Its other
        # branch can be a member selector, keyed by the same exact (b,t).
        sign, pred, _, x = rows[13][1]
        assert (sign, pred, x) == (True, 'E', 'x')
        rows[13][1] = g.E(g.f('Z', 'b', 't', 'x'), 'x')
    if evaluation_member:
        rows[13][1] = g.E(g.f('V', 'x', ('d',)), 'x')
    return rows


def completion(evaluation_transport=False):
    # Three rows only. Reflexivity follows from native row01 and the first row.
    # The optional fourth row reproduces the earlier RP19 control.
    rows = [
        [g.Eq('x', 'y', False), g.Eq('x', 'z', False), g.Eq('y', 'z')],
        [g.Eq('x0', 'y0', False), g.Eq('x1', 'y1', False),
         g.E('x0', 'x1', False), g.E('y0', 'y1')],
        [g.Eq(('d',), ('q',), False)],
    ]
    if evaluation_transport:
        rows.insert(1, [g.Eq('s', 't', False),
            g.Eq(g.f('V', 's', 'j'), g.f('V', 't', 'j'))])
    return rows


def clauses(extensional=False, fused_member=False, evaluation_transport=False,
            evaluation_member=False):
    return native(extensional, fused_member, evaluation_member) + completion(evaluation_transport)


def signature(fused_member=False):
    return [(f, a) for f, a in FUNCTIONS if not (fused_member and f == 'D')]


def canonical(rows):
    out = []
    for row in rows:
        rename = {v: 'v' + str(i) for i, v in enumerate(g.clause_variables(row))}
        def term(t):
            return rename[t] if isinstance(t, str) else (t[0],) + tuple(term(a) for a in t[1:])
        out.append([(s, p, term(a), term(b)) for s, p, a, b in row])
    return out


def encode_template(rows, fs):
    # Four variable slots, two constants, and at most ten functions = 16 codes.
    opnames = CONSTANTS + [n for n, _ in fs]
    if 4 + len(opnames) > 16:
        raise ValueError('signature does not fit declared four-bit format')
    opcodes = {n: i + 4 for i, n in enumerate(opnames)}
    out = ''
    for row in rows:
        vs = {v: i for i, v in enumerate(g.clause_variables(row))}
        if len(vs) > 4 or not 1 <= len(row) <= 7:
            raise ValueError('clause exceeds template format')
        def term(t):
            if isinstance(t, str):
                return format(vs[t], '04b')
            return format(opcodes[t[0]], '04b') + ''.join(term(x) for x in t[1:])
        out += format(len(row), '03b')
        for s, p, a, b in row:
            out += str(int(s)) + format(PREDICATES.index(p), '02b') + term(a) + term(b)
    return out + '000'


def decode_template(bits, fs):
    # Independent cursor parser: the recursive encoding routine is not used.
    tags = [(n, 0) for n in CONSTANTS] + list(fs)
    cursor = 0
    def take(n):
        nonlocal cursor
        if cursor + n > len(bits):
            raise ValueError('truncated template')
        part = bits[cursor:cursor+n]
        cursor += n
        if any(c not in '01' for c in part):
            raise ValueError('invalid binary digit')
        return int(part, 2)
    def term():
        op = take(4)
        if op < 4:
            return 'v' + str(op)
        if op - 4 >= len(tags):
            raise ValueError('unused opcode')
        n, arity = tags[op - 4]
        return (n,) + tuple(term() for _ in range(arity))
    rows = []
    while True:
        length = take(3)
        if not length:
            if cursor != len(bits):
                raise ValueError('trailing template data')
            return rows
        row = []
        for _ in range(length):
            s, p = bool(take(1)), PREDICATES[take(2)]
            row.append((s, p, term(), term()))
        rows.append(row)


def term_code(t, fs):
    if len(t) == 1:
        if t[0] in CONSTANTS:
            return CONSTANTS.index(t[0])
        raise ValueError('unknown constant')
    tags = {n: i for i, (n, _) in enumerate(fs)}
    tag = tags[t[0]] if t[0] in tags else int(t[0][4:])
    return 2 + tag + 16 * g.tuple_code([term_code(a, fs) for a in t[1:]])


def term_decode(code, fs):
    if code < 2:
        return (CONSTANTS[code],)
    tag, payload = (code - 2) % 16, (code - 2) // 16
    n, arity = fs[tag] if tag < len(fs) else ('junk' + str(tag), 1)
    xs = g.tuple_decode(payload, arity)
    assert all(x < code for x in xs)
    return (n,) + tuple(term_decode(x, fs) for x in xs)


def ground_term(t, env, fs):
    if isinstance(t, str):
        return env[t]
    if len(t) == 1:
        return CONSTANTS.index(t[0])
    tag = next(i for i, (n, _) in enumerate(fs) if n == t[0])
    return 2 + tag + 16 * g.tuple_code([ground_term(a, env, fs) for a in t[1:]])


def stage_cnf(rows, fs, bound):
    """All variables take every code 0..bound, with no equality assumptions.

    Eq is an ordinary fourth propositional predicate in this reduced theory.
    No deleted congruence is reintroduced by a finite equality solver.
    """
    for row in rows:
        vs = g.clause_variables(row)
        for values in product(range(bound + 1), repeat=len(vs)):
            env = dict(zip(vs, values))
            yield tuple((1 if s else -1) * (1 + PREDICATES.index(p) + 4 * g.pair(
                ground_term(a, env, fs), ground_term(b, env, fs)))
                for s, p, a, b in row)


def variant_name(extensional=False, fused_member=False, evaluation_transport=False,
                 evaluation_member=False):
    count = 18 + int(extensional) + int(evaluation_transport)
    return 'RP' + str(count) + ('E' if extensional else '') + ('V' if evaluation_member else 'Z' if fused_member else 'D')


def emit(output, evaluation_transport=False):
    output.mkdir(parents=True, exist_ok=True)
    results = {'status': 'exact payload and finite reference checks; no binary TM', 'variants': {}}
    targets = [(ext, fused, False) for ext, fused in product((False, True), repeat=2)]
    if not evaluation_transport:
        targets.append((False, False, True))
    for extensional, fused, evaluation_member in targets:
        name = variant_name(extensional, fused, evaluation_transport, evaluation_member)
        rows = clauses(extensional, fused, evaluation_transport, evaluation_member)
        fs = signature(fused or evaluation_member)
        bits = encode_template(rows, fs)
        assert decode_template(bits, fs) == canonical(rows)
        for n in range(2048):
            assert term_code(term_decode(n, fs), fs) == n
        node_count = sum(g.term_nodes(t) for row in rows for lit in row for t in lit[2:])
        literal_count = sum(map(len, rows))
        assert len(bits) == 3 * len(rows) + 3 * literal_count + 4 * node_count + 3
        ground = tuple(stage_cnf(rows, fs, 0))
        witness = g.solve(ground)
        if witness is not None:
            assert g.valuation_satisfies(ground, witness)
        metrics = {'clauses': len(rows), 'literals': literal_count,
            'term_nodes': node_count, 'template_bits': len(bits),
            'packed_bytes': (len(bits) + 7) // 8, 'padding_bits': (-len(bits)) % 8,
            'constants': len(CONSTANTS), 'proper_functions': len(fs),
            'max_variables': max(map(lambda row: len(g.clause_variables(row)), rows)),
            'max_term_depth': max(g.term_depth(t) for row in rows for lit in row for t in lit[2:]),
            'bit_sha256': hashlib.sha256(bits.encode()).hexdigest(),
            'template_round_trip': True, 'term_codec_round_trips': 2048,
            'actual_stage_0': {'clauses': len(ground), 'verdict': 'SAT' if witness is not None else 'UNSAT',
                'atoms': len({abs(l) for row in ground for l in row}),
                'checked_valuation': witness is not None}}
        (output / (name + '.json')).write_text(json.dumps({'name': name, 'constants': CONSTANTS,
            'functions': fs, 'predicates': PREDICATES, 'clauses': rows, 'metrics': metrics}, indent=2) + '\n')
        (output / (name + '.bits')).write_text(bits + '\n')
        packed = bits + '0' * ((-len(bits)) % 8)
        (output / (name + '.bin')).write_bytes(bytes(int(packed[i:i+8], 2) for i in range(0, len(packed), 8)))
        results['variants'][name] = metrics
    results['prior'] = {'source44_FC15_complete_bits': 1616,
        'source44_FC16_complete_bits': 1823,
        'incoming_U15_circle_bits': 1134, 'incoming_U16_circle_bits': 1341}
    (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, default=HERE / 'results')
    ap.add_argument('--stage', type=int)
    ap.add_argument('--extensional', action='store_true')
    ap.add_argument('--fused-member', action='store_true')
    ap.add_argument('--evaluation-member', action='store_true',
                    help='use V(x,d) as the member-selector term (RP18V)')
    ap.add_argument('--evaluation-transport', action='store_true',
                    help='restore first-argument V congruence for the earlier RP19 control')
    args = ap.parse_args()
    results = emit(args.output, args.evaluation_transport)
    if args.stage is not None:
        if args.stage < 0:
            ap.error('stage must be nonnegative')
        rows = clauses(args.extensional, args.fused_member, args.evaluation_transport, args.evaluation_member)
        fs = signature(args.fused_member or args.evaluation_member)
        cnf = tuple(stage_cnf(rows, fs, args.stage))
        witness = g.solve(cnf)
        if witness is not None:
            assert g.valuation_satisfies(cnf, witness)
        result = {'bound': args.stage, 'clauses': len(cnf),
            'atoms': len({abs(l) for row in cnf for l in row}),
            'verdict': 'SAT' if witness is not None else 'UNSAT'}
        (args.output / 'requested-stage.json').write_text(json.dumps(result, indent=2) + '\n')
        results['requested_stage'] = result
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
