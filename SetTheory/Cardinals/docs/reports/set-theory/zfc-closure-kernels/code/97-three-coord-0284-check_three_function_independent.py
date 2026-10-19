#!/usr/bin/env python3
"""Independent symbolic expansion and fixed-opcode check of the 999-bit input.

This checker imports neither the transformation nor its encoder. It starts
from the separately regenerated SE19/SE20 JSON and implements the stated
definitional substitutions directly. It checks data, not a mathematical
consistency proof or Turing-machine state count.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

D = ['d']
Q = ['A', D, D]
R = ['C', D, D, D]
S = ['C', D, D, Q]


def expand(t):
    if isinstance(t, str):
        return t
    op, *tail = t
    if op == 'd':
        return D
    if op == 'q':
        return Q
    x = [expand(a) for a in tail]
    if op == 'N':
        return ['C', D, *x]
    if op == 'Q':
        return ['C', Q, *x]
    if op == 'H':
        return ['A', ['C', *x, D], D]
    if op == 'Y':
        return ['A', ['C', *x], Q]
    if op == 'W':
        return ['A', ['C', *x], R]
    if op == 'Z':
        return ['A', ['C', *x], S]
    if op not in ('V', 'C', 'A'):
        raise ValueError(op)
    return [op, *x]


def check(source, target):
    before = json.loads(source.read_text())
    expected = [[[sign, pred, expand(a), expand(b)]
                 for sign, pred, a, b in row] for row in before]
    actual = json.loads(target.with_suffix('.json').read_text())
    assert expected == actual, 'The explicit source substitution differs'
    output, node_count, polynomial = [], 0, Counter()
    for row in expected:
        variables = []
        def term(t):
            nonlocal node_count
            node_count += 1
            if isinstance(t, str):
                if t not in variables:
                    variables.append(t)
                i = variables.index(t)
                assert i < 4
                return f'{i:03b}'
            tag, arity = {'d': (4, 0), 'V': (5, 2),
                          'C': (6, 3), 'A': (7, 2)}[t[0]]
            assert len(t) == arity + 1
            return f'{tag:03b}' + ''.join(term(a) for a in t[1:])
        output.append(f'{len(row):03b}')
        for sign, pred, a, b in row:
            output.append(('1' if sign else '0') +
                          {'E': '00', 'Inc': '01', 'G': '10', 'Eq': '11'}[pred])
            output.extend((term(a), term(b)))
        polynomial[len(variables)] += 1
    bits = ''.join(output) + '000'
    assert bits == target.with_suffix('.bits').read_text().strip()
    raw = ''.join(f'{b:08b}' for b in target.with_suffix('.bin').read_bytes())
    assert raw == bits + '0' * (-len(bits) % 8)
    return dict(status='PASS', clauses=len(expected),
                literals=sum(map(len, expected)), term_nodes=node_count,
                bits=len(bits), packed_bytes=len(raw) // 8,
                ground_polynomial=dict(sorted(polynomial.items())),
                payload_sha256=hashlib.sha256(bits.encode()).hexdigest(),
                packed_sha256=hashlib.sha256(target.with_suffix('.bin').read_bytes()).hexdigest())


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--formalism-results', type=Path, required=True)
    p.add_argument('--three-results', type=Path, required=True)
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    results = {}
    for n, size, nodes in ((19, 999, 268), (20, 1182, 324)):
        result = check(a.formalism_results / f'fc{n}_named.json',
                       a.three_results / f'se{n}_three_functions_one_constant')
        assert result['bits'] == size and result['term_nodes'] == nodes
        results[f'SE{n}-3'] = result
    body = json.dumps(results, indent=2) + '\n'
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(body)
    print(body)


if __name__ == '__main__':
    main()
