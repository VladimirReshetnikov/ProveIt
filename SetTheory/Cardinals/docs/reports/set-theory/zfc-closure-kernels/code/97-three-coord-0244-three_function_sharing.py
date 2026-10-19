#!/usr/bin/env python3
"""Exact finite-theory payloads for the V,C,A product-model reduction.

This is a self-contained AST transformation and independent prefix parser.
It makes no Turing-machine state claim.  The input file contains the already
completed SE19/SE20 theory, including precisely its four Eq clauses.

Usage: python3 three_function_sharing.py [--output three_function_results]
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path

import three_function_runtime as K

HERE = Path(__file__).resolve().parent
FUNCTIONS = [('V', 2), ('C', 3), ('A', 2)]
PREDICATES = ['E', 'Inc', 'G', 'Eq']
D, Q = ('d',), ('q',)
R, H = ('C', D, D, D), ('C', D, D, Q)


def freeze(t):
    return tuple(freeze(x) for x in t) if isinstance(t, list) else t


def lower_term(t):
    if isinstance(t, str) or len(t) == 1:
        return t
    name, *args = t
    args = tuple(map(lower_term, args))
    if name == 'N':
        return ('C', D, *args)
    if name == 'Q':
        return ('C', Q, *args)
    if name == 'H':
        return ('A', ('C', *args, D), D)
    if name == 'Y':
        return ('A', ('C', *args), Q)
    if name == 'W':
        return ('A', ('C', *args), R)
    if name == 'Z':
        return ('A', ('C', *args), H)
    assert name in dict(FUNCTIONS), name
    return (name, *args)


def eliminate_q(t):
    if t == Q:
        return ('A', D, D)
    if isinstance(t, str):
        return t
    return (t[0],) + tuple(eliminate_q(x) for x in t[1:])


def transform(rows, one_constant):
    def term(t):
        t = lower_term(t)
        return eliminate_q(t) if one_constant else t
    return [[(sign, pred, term(a), term(b)) for sign, pred, a, b in row]
            for row in rows]


def variables(row):
    names = []
    def visit(t):
        if isinstance(t, str):
            if t not in names:
                names.append(t)
        else:
            for x in t[1:]:
                visit(x)
    for _, _, a, b in row:
        visit(a)
        visit(b)
    return names


def nodes(t):
    return 1 if isinstance(t, str) else 1 + sum(map(nodes, t[1:]))


def depth(t):
    return 0 if isinstance(t, str) or len(t) == 1 else 1 + max(map(depth, t[1:]))


def canonical(rows):
    result = []
    for row in rows:
        names = {v: 'v' + str(i) for i, v in enumerate(variables(row))}
        def ren(t):
            return names[t] if isinstance(t, str) else (t[0],) + tuple(map(ren, t[1:]))
        result.append([(s, p, ren(a), ren(b)) for s, p, a, b in row])
    return result


def encode(rows, one_constant):
    constants = [D] if one_constant else [D, Q]
    width = 3 if one_constant else 4
    tags = {name: 4 + len(constants) + i for i, (name, _) in enumerate(FUNCTIONS)}
    pieces = []
    for row in rows:
        names = {v: i for i, v in enumerate(variables(row))}
        assert len(names) <= 4 and 0 < len(row) < 8
        def term(t):
            if isinstance(t, str):
                return format(names[t], f'0{width}b')
            if t in constants:
                return format(4 + constants.index(t), f'0{width}b')
            assert len(t) - 1 == dict(FUNCTIONS)[t[0]]
            return format(tags[t[0]], f'0{width}b') + ''.join(term(x) for x in t[1:])
        pieces.append(format(len(row), '03b'))
        for sign, pred, a, b in row:
            pieces.extend((str(int(sign)), format(PREDICATES.index(pred), '02b'), term(a), term(b)))
    return ''.join(pieces) + '000'


def decode(bits, one_constant):
    """Cursor decoder.  It does not use the source AST or encoder internals."""
    constants = [('d', 0)] if one_constant else [('d', 0), ('q', 0)]
    signature = constants + [('V', 2), ('C', 3), ('A', 2)]
    width = 3 if one_constant else 4
    pos = 0
    def read(n):
        nonlocal pos
        if pos + n > len(bits):
            raise ValueError('truncated stream')
        fragment = bits[pos:pos+n]
        if any(c not in '01' for c in fragment):
            raise ValueError('nonbinary stream')
        pos += n
        return int(fragment, 2)
    def term():
        opcode = read(width)
        if opcode < 4:
            return 'v' + str(opcode)
        if opcode - 4 >= len(signature):
            raise ValueError('unused opcode')
        name, arity = signature[opcode - 4]
        return (name,) + tuple(term() for _ in range(arity))
    rows = []
    while True:
        n = read(3)
        if not n:
            if pos != len(bits):
                raise ValueError('trailing bits')
            return rows
        row = []
        for _ in range(n):
            sign, pred = bool(read(1)), ['E', 'Inc', 'G', 'Eq'][read(2)]
            row.append((sign, pred, term(), term()))
        rows.append(row)


def metrics(rows, bits, one_constant):
    terms = [t for row in rows for literal in row for t in literal[2:]]
    return {
        'clauses': len(rows),
        'literals': sum(map(len, rows)),
        'term_nodes': sum(map(nodes, terms)),
        'maximum_term_depth': max(map(depth, terms)),
        'maximum_variables': max(len(variables(row)) for row in rows),
        'ground_instance_polynomial_by_degree': dict(sorted(Counter(len(variables(row)) for row in rows).items())),
        'constants': 1 if one_constant else 2,
        'proper_functions': 3,
        'function_arities': dict(FUNCTIONS),
        'predicate_symbols_including_Eq': 4,
        'term_opcode_bits': 3 if one_constant else 4,
        'payload_bits': len(bits),
        'packed_bytes': (len(bits) + 7) // 8,
        'padding_bits': -len(bits) % 8,
        'payload_sha256': hashlib.sha256(bits.encode()).hexdigest(),
    }


def decode_number(number):
    """Bijection N -> ground terms with one added, unused unary constructor."""
    if number < 0:
        raise ValueError('negative term code')
    if number == 0:
        return D
    tag, body = (number - 1) % 4, (number - 1) // 4
    name, arity = FUNCTIONS[tag] if tag < 3 else ('padding', 1)
    children = K.tuple_decode(body, arity)
    assert all(child < number for child in children)
    return (name,) + tuple(decode_number(n) for n in children)


def encode_number(tree):
    if tree == D:
        return 0
    tags = {name: i for i, (name, _) in enumerate(FUNCTIONS)}
    tag = 3 if tree[0] == 'padding' else tags[tree[0]]
    arity = 1 if tag == 3 else FUNCTIONS[tag][1]
    if len(tree) != 1 + arity:
        raise ValueError('incorrect arity')
    return 1 + tag + 4 * K.tuple_code([encode_number(t) for t in tree[1:]])


def ground_term(tree, environment):
    if isinstance(tree, str):
        return environment[tree]
    if tree == D:
        return 0
    tags = {name: i for i, (name, _) in enumerate(FUNCTIONS)}
    return 1 + tags[tree[0]] + 4 * K.tuple_code([ground_term(t, environment) for t in tree[1:]])


def ground_rows(rows, frontier):
    for row in rows:
        names = variables(row)
        for values in itertools.product(frontier, repeat=len(names)):
            environment = dict(zip(names, values))
            yield tuple((1 if sign else -1) * (1 + K.atom_code(
                pred, ground_term(a, environment), ground_term(b, environment)))
                for sign, pred, a, b in row)


def load_rows(extensional=False):
    source = HERE / ('three_function_se20_input.json' if extensional else 'three_function_se19_input.json')
    return transform(freeze(json.loads(source.read_text())), True)


def decide_stage(n, extensional=False):
    """Exactly decide every substitution of ground codes 0..n.

    Generated endpoints are retained even if their term codes exceed n.
    Eq is an ordinary propositional atom; no equality algorithm is added.
    Exceptions/resource errors propagate and are never classified as UNSAT.
    """
    if n < 0:
        raise ValueError('negative stage')
    cnf = list(ground_rows(load_rows(extensional), range(n + 1)))
    witness = K.solve(cnf)
    assert witness is None or K.valuation_satisfies(cnf, witness)
    return {
        'stage': n, 'extensional': extensional,
        'status': 'UNSAT' if witness is None else 'SAT',
        'ground_instances': len(cnf),
        'distinct_atoms': len({abs(lit) for row in cnf for lit in row}),
        'maximum_atom_code_bits': max(abs(lit).bit_length() for row in cnf for lit in row),
        'checked_witness_literals': 0 if witness is None else len(witness),
        'scope': 'One exact finite CNF, not a model of the whole theory or a consistency proof',
    }


def whole_search(extensional=False):
    """Halt exactly on a finite refutation; otherwise run indefinitely."""
    for n in itertools.count():
        result = decide_stage(n, extensional)
        print(json.dumps(result), flush=True)
        if result['status'] == 'UNSAT':
            return result


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    report = {
        'scope': 'Exact finite-theory transformation and codec; no binary TM or state-count claim',
        'derived_terms': {
            'q_in_one_constant_signature': ['A', ['d'], ['d']],
            'N(a,b)': ['C', ['d'], 'a', 'b'],
            'Q(j,a)': ['C', ['q'], 'j', 'a'],
            'H(b,t)': ['A', ['C', 'b', 't', ['d']], ['d']],
            'Y(b,t,u)': ['A', ['C', 'b', 't', 'u'], ['q']],
            'W(s,j,a)': ['A', ['C', 's', 'j', 'a'], R],
            'Z(b,t,u)': ['A', ['C', 'b', 't', 'u'], H],
        },
        'source_sha256': {}, 'theories': {}, 'malformed_streams_rejected': 0,
        'ground_term_codec': {
            'radix': 4, 'constant_code': 0,
            'constructor_tags': {'V': 0, 'C': 1, 'A': 2, 'padding_unary': 3},
            'formula': '1 + tag + 4 * right_nested_Cantor_tuple(children)',
        },
    }
    for base in ('se19', 'se20'):
        source = HERE / ('three_function_' + base + '_input.json')
        data = source.read_bytes()
        report['source_sha256'][source.name] = hashlib.sha256(data).hexdigest()
        native = freeze(json.loads(data))
        for one in (False, True):
            name = base + '_three_functions_' + ('one_constant' if one else 'named')
            rows = transform(native, one)
            bits = encode(rows, one)
            assert decode(bits, one) == canonical(rows)
            result = metrics(rows, bits, one)
            assert result['payload_bits'] == 3 * result['clauses'] + 3 * result['literals'] + result['term_opcode_bits'] * result['term_nodes'] + 3
            for malformed in (bits[:-1], bits + '0', bits[:19], 'x' + bits[1:]):
                try:
                    decode(malformed, one)
                except ValueError:
                    report['malformed_streams_rejected'] += 1
                else:
                    raise AssertionError('malformed input accepted')
            report['theories'][name] = result
            (output / (name + '.json')).write_text(json.dumps(rows, indent=2) + '\n')
            (output / (name + '.bits')).write_text(bits + '\n')
            padded = bits + '0' * (-len(bits) % 8)
            (output / (name + '.bin')).write_bytes(int(padded, 2).to_bytes(len(padded) // 8, 'big'))
    for number in range(4096):
        assert encode_number(decode_number(number)) == number
    report['numeric_term_code_roundtrips'] = 4096
    ground_checks = 0
    for extensional in (False, True):
        for row in load_rows(extensional):
            names = variables(row)
            for values in itertools.product(range(3), repeat=len(names)):
                environment = dict(zip(names, values))
                def substitute(t):
                    if isinstance(t, str):
                        return decode_number(environment[t])
                    return (t[0],) + tuple(substitute(x) for x in t[1:])
                for _, _, a, b in row:
                    for t in (a, b):
                        assert ground_term(t, environment) == encode_number(substitute(t))
                        ground_checks += 1
    report['independent_ground_substitution_checks'] = ground_checks
    report['finite_stage_controls'] = [decide_stage(n, extensional)
                                      for extensional in (False, True) for n in (0, 1)]
    assert all(control['status'] == 'SAT' for control in report['finite_stage_controls'])
    (output / 'metrics.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE / 'three_function_results')
    parser.add_argument('--stage', type=int, help='decide one complete finite stage in the one-constant theory')
    parser.add_argument('--whole-search', action='store_true', help='run the fair inconsistency semidecision procedure')
    parser.add_argument('--extensional', action='store_true', help='use the SE20 extensional control for a stage/search')
    args = parser.parse_args()
    if args.stage is not None:
        if args.stage < 0 or args.whole_search:
            parser.error('stage must be nonnegative and cannot accompany --whole-search')
        print(json.dumps(decide_stage(args.stage, args.extensional), indent=2))
    elif args.whole_search:
        whole_search(args.extensional)
    else:
        run(args.output)
