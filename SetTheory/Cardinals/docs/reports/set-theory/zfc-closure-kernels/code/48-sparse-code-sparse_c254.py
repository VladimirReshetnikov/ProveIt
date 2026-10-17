#!/usr/bin/env python3
"""Exact demand-driven checker for the pinned C254 numerical proof syntax.

The arithmetic formula constructors are exported from ProveIt's Code254.lean.
The reference checker below separately mirrors RawProof/decodeFuel/valid.
No claim is made that this Python program is a binary Turing-machine compiler.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
import json
from math import isqrt
from pathlib import Path
import random
import re
import time

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / 'data'


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


PRIMITIVES = {
    'wim': lambda a, b: 4 * pair(a, b),
    'wel': lambda a, b: 4 * pair(a, b) + 1,
    'wal': lambda a, b: 4 * pair(a, b) + 2,
    'weq': lambda a, b: 4 * pair(a, b) + 3,
}
ARITY = {'wim': 2, 'wel': 2, 'wal': 2, 'weq': 2, 'wn': 1, 'wa': 2,
         'wex': 2, 'bundleC': 3, 'bundleG': 3, 'bundle': 3,
         **{f'rho{i}': (2 if i in (1, 6) else 4 if i == 8 else 3)
            for i in range(1, 9)}}


def export_formulas(source: str) -> dict:
    """Read the actual fixed prefix expressions, without executing Lean text."""
    result = {}
    for name in ['wn', 'wa', 'wex'] + [f'rho{i}' for i in range(1, 9)] + ['bundleC', 'bundleG', 'bundle']:
        match = re.search(r'^def ' + name + r'\b.*?:=\s*(.*?)(?=\n(?:def |theorem |/--|/-!|inductive ))', source, re.M | re.S)
        if not match:
            raise ValueError(f'missing definition {name}')
        expr = match.group(1).strip()
        tokens = re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[()]|\d+', expr)
        position = 0

        def parse():
            nonlocal position
            token = tokens[position]
            position += 1
            if token == '(':
                node = parse()
                if tokens[position] != ')':
                    raise ValueError(f'bad closing token in {name}')
                position += 1
                return node
            if token in ARITY:
                return [token] + [parse() for _ in range(ARITY[token])]
            if token == 'F':
                return 1
            if token.isdigit():
                return int(token)
            if token not in ('a', 'b', 'c', 'u', 'x'):
                raise ValueError(f'unknown token {token} in {name}')
            return token

        tree = parse()
        if position != len(tokens):
            raise ValueError(f'unconsumed tokens in {name}: {tokens[position:]}')
        params = {'wn': ['a'], 'wa': ['a', 'b'], 'wex': ['x', 'a']}.get(name)
        if params is None:
            params = ['a', 'b', 'c', 'u'][:ARITY[name]]
        result[name] = {'params': params, 'tree': tree}
    return result


class FormulaArithmetic:
    def __init__(self, definitions: dict):
        self.definitions = definitions

    def evaluate(self, tree, env):
        if isinstance(tree, int):
            return tree
        if isinstance(tree, str):
            return env[tree]
        return self.call(tree[0], *(self.evaluate(a, env) for a in tree[1:]))

    def call(self, name: str, *args: int) -> int:
        if name in PRIMITIVES:
            return PRIMITIVES[name](*args)
        entry = self.definitions[name]
        return self.evaluate(entry['tree'], dict(zip(entry['params'], args)))


def fields(code: int):
    payload, tag = divmod(code - 1, 12)
    a, tail = unpair(payload)
    b, d = unpair(tail)
    e, f = unpair(d)
    return tag, payload, a, tail, b, d, e, f


def children(code: int) -> tuple[int, ...]:
    if code == 0:
        return ()
    tag, _, _, tail, b, d, _, _ = fields(code)
    return (b, d) if tag == 1 else (tail,) if tag == 2 else ()


def row(code: int, lookup, arithmetic: FormulaArithmetic) -> int:
    """0 is invalid; n+1 means a valid proof of formula code n."""
    if code == 0:
        return 0
    tag, payload, a, tail, b, d, e, f = fields(code)
    if tag == 0:
        return int(payload == 0)
    if tag == 1:
        if not (b < code and d < code):
            return 0
        minor, major = lookup(b), lookup(d)
        return a + 1 if minor and major and major - 1 == 4 * pair(minor - 1, a) else 0
    if tag == 2:
        value = lookup(tail) if tail < code else 0
        return 4 * pair(a, value - 1) + 3 if value else 0
    if tag in (3, 8):
        return arithmetic.call('rho1' if tag == 3 else 'rho6', a, tail) + 1
    if tag in (4, 5, 6, 7, 9):
        return arithmetic.call(f'rho{tag - 2}', a, b, d) + 1
    if tag == 10:
        return arithmetic.call('rho8', a, b, e, f) + 1
    if d == a or d == b:
        return 0
    return arithmetic.call('bundle', a, b, d) + 1


def demand_codes(code: int) -> list[int]:
    if not isinstance(code, int) or code < 0:
        raise ValueError('proof code must be a natural number')
    seen, work = {0}, [code]
    while work:
        c = work.pop()
        if c in seen:
            continue
        seen.add(c)
        for child in children(c):
            if not 0 <= child < c:
                raise AssertionError('nondecreasing dependency')
            work.append(child)
    return sorted(seen)


def sparse_history(code: int, arithmetic: FormulaArithmetic) -> list[tuple[int, int]]:
    values = {}
    for c in demand_codes(code):
        values[c] = row(c, values.__getitem__, arithmetic)
    return list(values.items())


def check(code: int, conclusion: int, arithmetic: FormulaArithmetic) -> bool:
    return conclusion >= 0 and sparse_history(code, arithmetic)[-1][1] == conclusion + 1


def verify_certificate(code: int, certificate: list[tuple[int, int]], arithmetic: FormulaArithmetic) -> int | None:
    """Verify sorted rows; reject missing children, forged values and extra tails."""
    if not certificate or certificate[0] != (0, 0) or certificate[-1][0] != code:
        return None
    values, previous = {}, -1
    try:
        for c, v in certificate:
            if c <= previous or c < 0 or v < 0:
                return None
            if row(c, values.__getitem__, arithmetic) != v:
                return None
            values[c] = v
            previous = c
    except (KeyError, ValueError):
        return None
    return values[code]


def reference_decode(code: int):
    """Independent finite tree transcription of decodeStep/decodeFuel."""
    if code == 0:
        return None
    payload, tag = divmod(code - 1, 12)
    x, rest = unpair(payload)
    y, z = unpair(rest)
    if tag == 0:
        return ('truth',) if payload == 0 else None
    if tag == 1:
        left, right = reference_decode(y), reference_decode(z)
        return None if left is None or right is None else ('mp', x, left, right)
    if tag == 2:
        p = reference_decode(rest)
        return None if p is None else ('gen', x, p)
    if tag in (3, 8):
        return ('rho1' if tag == 3 else 'rho6', x, rest)
    if tag in (4, 5, 6, 7, 9):
        return (f'rho{tag - 2}', x, y, z)
    if tag == 10:
        z1, z2 = unpair(z)
        return ('rho8', x, y, z1, z2)
    return ('bundle', x, y, z)


def reference_value(tree, arithmetic: FormulaArithmetic):
    if tree is None:
        return None
    name, *args = tree
    if name == 'truth':
        return 0
    if name == 'mp':
        output, p, q = args
        minor, major = reference_value(p, arithmetic), reference_value(q, arithmetic)
        if minor is None or major is None or major != 4 * pair(minor, output):
            return None
        return output
    if name == 'gen':
        a, p = args
        value = reference_value(p, arithmetic)
        return None if value is None else PRIMITIVES['wal'](a, value)
    if name == 'bundle' and (args[2] == args[0] or args[2] == args[1]):
        return None
    return arithmetic.call(name, *args)


def occurrence_count(code: int) -> int:
    return 0 if code == 0 else 1 + sum(occurrence_count(x) for x in children(code))


def quote(tree) -> int:
    name, *args = tree
    if name == 'truth':
        return 1
    if name == 'mp':
        out, p, q = args
        return 12 * pair(out, pair(quote(p), quote(q))) + 2
    if name == 'gen':
        binder, p = args
        return 12 * pair(binder, quote(p)) + 3
    tag = {'rho1': 3, 'rho2': 4, 'rho3': 5, 'rho4': 6, 'rho5': 7, 'rho6': 8,
           'rho7': 9, 'rho8': 10, 'bundle': 11}[name]
    payload = args[-1]
    for a in reversed(args[:-1]):
        payload = pair(a, payload)
    return 12 * payload + tag + 1


def beta(b: int, c: int, i: int) -> int:
    return b % (1 + (i + 1) * c)


def beta_encode(values: list[int]) -> tuple[int, int]:
    """Construct the standard CRT certificate, used only on small witnesses."""
    from math import factorial
    c = (max(values, default=0) + 1) * factorial(len(values))
    b, modulus = 0, 1
    for i, value in enumerate(values):
        m = 1 + (i + 1) * c
        b += modulus * (((value - b) * pow(modulus, -1, m)) % m)
        modulus *= m
    assert all(beta(b, c, i) == v for i, v in enumerate(values))
    return b, c


def self_test(arithmetic: FormulaArithmetic, exhaustive: int = 72):
    start = time.perf_counter()
    pair_tests = 0
    for a in range(32):
        for b in range(32):
            assert unpair(pair(a, b)) == (a, b)
            pair_tests += 1
    for c in range(10000):
        assert pair(*unpair(c)) == c
    max_occ = 0
    for c in range(20000):
        n = occurrence_count(c)
        assert n * (n + 2) <= 3 * c.bit_length()
        max_occ = max(max_occ, n)
    numeric_cases = 0
    max_bits = 0
    for c in range(exhaustive):
        cert = sparse_history(c, arithmetic)
        result = reference_value(reference_decode(c), arithmetic)
        expected = 0 if result is None else result + 1
        assert cert[-1][1] == expected
        assert verify_certificate(c, cert, arithmetic) == expected
        assert len(cert) <= isqrt(3 * c.bit_length() + 1)
        max_bits = max(max_bits, *(v.bit_length() for _, v in cert))
        forged = cert[:-1] + [(cert[-1][0], cert[-1][1] + 1)]
        assert verify_certificate(c, forged, arithmetic) is None
        numeric_cases += 1
    truth = ('truth',)
    valid_mp = ('mp', 0, truth, truth)  # Imp(0,0)=0 is the intended alias.
    examples = [truth, valid_mp, ('gen', 0, valid_mp), ('mp', 1, truth, truth),
                ('bundle', 0, 0, 0), ('bundle', 1, 1, 0)]
    examples += [(f'rho{i}', *([0] * (2 if i in (1, 6) else 4 if i == 8 else 3))) for i in range(1, 9)]
    large_examples = []
    for h in range(7):
        t = truth
        for _ in range(h):
            t = ('mp', 0, t, t)
        c = quote(t)
        cert = sparse_history(c, arithmetic)
        n = occurrence_count(c)
        assert cert[-1][1] == 1 and n * (n + 2) <= 3 * c.bit_length()
        large_examples.append({'height': h, 'input_bits': c.bit_length(),
                               'unfolded_nodes': n, 'sparse_rows': len(cert),
                               'dense_rows_decimal_digits': len(str(c + 1)) if c.bit_length() < 14000 else None})
    for tree in examples:
        c = quote(tree)
        assert reference_decode(c) == tree
        expected = reference_value(tree, arithmetic)
        cert = sparse_history(c, arithmetic)
        assert cert[-1][1] == (0 if expected is None else expected + 1)
        if len(cert) > 2:
            missing = [r for r in cert if r[0] != cert[-2][0]]
            assert verify_certificate(c, missing, arithmetic) is None
    beta_cases = [[0], [0, 1, 0, 2], [7, 3, 9], [0, 0, 0, 0]]
    for values in beta_cases:
        b, c = beta_encode(values)
        assert [beta(b, c, i) for i in range(len(values))] == values
    return {'status': 'passed', 'pair_roundtrips': pair_tests,
            'unpair_roundtrips': 10000, 'all_input_node_bound_checks': 20000,
            'max_nodes_in_small_codes': max_occ, 'all_input_numeric_cases': numeric_cases,
            'forged_value_rejections': numeric_cases, 'tagged_examples': len(examples),
            'beta_examples': len(beta_cases), 'max_small_output_bits': max_bits,
            'balanced_truth_proofs': large_examples,
            'elapsed_seconds': round(time.perf_counter() - start, 4),
            'scope': 'Executable regression; all-input correctness and complexity are proved in report.tex. No new Lean or binary compiler theorem.'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--export-lean', type=Path)
    parser.add_argument('--test', action='store_true')
    parser.add_argument('--exhaustive', type=int, default=72)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    DATA.mkdir(parents=True, exist_ok=True)
    if args.export_lean:
        raw = args.export_lean.read_bytes()
        definitions = export_formulas(raw.decode())
        (DATA / 'formula_circuits.json').write_text(json.dumps({'source_sha256': hashlib.sha256(raw).hexdigest(),
                                                             'definitions': definitions}, indent=2) + '\n')
    definitions = json.loads((DATA / 'formula_circuits.json').read_text())['definitions']
    arithmetic = FormulaArithmetic(definitions)
    if args.test:
        result = self_test(arithmetic, args.exhaustive)
        if args.output:
            args.output.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
