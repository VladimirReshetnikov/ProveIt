#!/usr/bin/env python3
"""Exact, fully charged structural-sharing variants of ProveIt's source-79 kernel.

The new source-level identity is J = P: an environment cons also constructs a
class NAND.  This is a consistency-preserving specialization with an explicit
countable upper model, not an equivalence of arbitrary original models.
The separate note supplies that ordinary proof.  No binary TM is generated.

Input: stack_kernel_source79.py, copied unchanged from ProveIt commit
13ec39ed43148b1807f51ed6e6528e1c84659562, MIT-0; see ATTRIBUTION.txt.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path

import stack_kernel_source79 as base


def rewrite_term(term, aliases):
    if isinstance(term, str):
        return term
    return (aliases.get(term[0], term[0]),
            *(rewrite_term(x, aliases) for x in term[1:]))


def transform(source, *, cons_nand, truth_fusion, spare_witness=None):
    data = copy.deepcopy(source)
    aliases = {}
    if cons_nand:
        aliases['J'] = 'P'
    if truth_fusion:
        aliases['top'] = 'd'
    assert spare_witness in (None, 'Pick', 'Q')
    if spare_witness:
        assert spare_witness in source['signature']
    def rw(term):
        if isinstance(term, str):
            return term
        children = tuple(rw(x) for x in term[1:])
        if term[0] == spare_witness:
            assert len(children) == 1
            return ('W', children[0], ('d',))
        return (aliases.get(term[0], term[0]), *children)
    data['equations'] = [tuple(map(rw, e)) for e in source['equations']]
    data['native_equations'] = [tuple(map(rw, e))
                                for e in source['native_equations']]
    data['groups'] = [(label, [[(lit[0], lit[1],
                              *(rw(x) for x in lit[2:])) for lit in clause]
                            for clause in clauses], tuple(map(rw, equation)))
                      for label, clauses, equation in source['groups']]
    data['signature'] = {s: arity for s, arity in source['signature'].items()
                         if s not in aliases and s != spare_witness}
    data['start'], data['target'] = rw(source['start']), rw(source['target'])
    data['name'] += ('_cons_nand' if cons_nand else '')
    data['name'] += ('_truth_fused' if truth_fusion else '')
    data['name'] += ('_spare_' + spare_witness.lower() if spare_witness else '')
    data['aliases'] = aliases
    data['spare_witness'] = spare_witness
    return data


def independent_prefix_decode(bits):
    """Second parser, using an explicit pending-arity stack for each term."""
    cursor = 0
    def take(width):
        nonlocal cursor
        chunk = bits[cursor:cursor + width]
        if len(chunk) != width or any(c not in '01' for c in chunk):
            raise ValueError('invalid or truncated bit field')
        cursor += width
        return int(chunk, 2)
    count = take(8)
    arities = [take(3) for _ in range(count)]
    capacity = take(8)
    width = max(1, (count + capacity - 1).bit_length())
    def term():
        stack = []
        while True:
            tag = take(width)
            if tag < capacity:
                result = 'v' + str(tag)
            elif tag >= count + capacity:
                raise ValueError('unused operation code')
            else:
                symbol = tag - capacity
                if arities[symbol]:
                    stack.append([symbol, arities[symbol], []])
                    continue
                result = (symbol,)
            while stack:
                frame = stack[-1]
                frame[2].append(result)
                frame[1] -= 1
                if frame[1]:
                    break
                stack.pop()
                result = (frame[0], *frame[2])
            else:
                return result
    equations = []
    while take(1):
        equations.append((term(), term()))
    start, target = term(), term()
    if cursor != len(bits):
        raise ValueError('trailing bits')
    if base.variables(start) | base.variables(target):
        raise ValueError('nonground query')
    return arities, capacity, equations, start, target


def verify(data):
    truth = data['target']
    assignments_checked = 0
    for _, clauses, equation in data['groups']:
        atoms = sorted({base.atom(lit) for clause in clauses for lit in clause},
                       key=repr)
        for bits in itertools.product((False, True), repeat=len(atoms)):
            valuation = dict(zip(atoms, bits))
            def val(term):
                if term == truth:
                    return True
                if term in valuation:
                    return valuation[term]
                assert term[0] == 'N'
                return not (val(term[1]) and val(term[2]))
            clause_value = all(any(valuation[base.atom(lit)] == lit[0]
                                   for lit in clause) for clause in clauses)
            assert clause_value == (val(equation[0]) == val(equation[1]))
            assignments_checked += 1
    bits, metrics = base.encode(data)
    decode = base.decode(bits)
    assert independent_prefix_decode(bits) == decode
    symbols = list(data['signature'])
    def erase(term):
        if isinstance(term, str):
            return term
        return (symbols.index(term[0]), *(erase(x) for x in term[1:]))
    assert decode == (list(data['signature'].values()), metrics['variable_capacity'],
                      [tuple(erase(x) for x in base.canonical(eq))
                       for eq in data['equations']],
                      erase(data['start']), erase(data['target']))
    truncations = 0
    for cut in range(len(bits)):
        for parser in (base.decode, independent_prefix_decode):
            try:
                parser(bits[:cut])
            except (ValueError, RecursionError):
                pass
            else:
                raise AssertionError(('accepted strict truncation', cut))
        truncations += 1
    for invalid in (bits + '0', bits[:-1] + 'x'):
        for parser in (base.decode, independent_prefix_decode):
            try:
                parser(invalid)
            except ValueError:
                pass
            else:
                raise AssertionError('accepted malformed packet')
    return bits, dict(metrics, boolean_assignments=assignments_checked,
                      independent_parsers=2, strict_truncations=truncations,
                      malformed_checks=4,
                      bits_sha256=hashlib.sha256(bits.encode()).hexdigest())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path,
                        default=Path(__file__).resolve().parent / 'generated')
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    report = {
        'status': 'finite packet verification; ordinary calibration supplied separately; no TM state count',
        'base_pin': '13ec39ed43148b1807f51ed6e6528e1c84659562',
        'source79_stack_projection_regressions': base.verify_stack(),
        'source79_formula_reification_regressions': base.verify_reification(),
        'variants': [],
    }
    configurations = [(derived, cons_nand, truth_fusion, None)
                      for derived, cons_nand, truth_fusion
                      in itertools.product((False, True), repeat=3)]
    configurations += [(False, True, True, role) for role in ('Pick', 'Q')]
    for derived, cons_nand, truth_fusion, spare_witness in configurations:
        data = transform(base.build(derived), cons_nand=cons_nand,
                         truth_fusion=truth_fusion, spare_witness=spare_witness)
        bits, metrics = verify(data)
        record = {'name': data['name'], 'derived_pick': derived,
                  'cons_nand': cons_nand, 'truth_fusion': truth_fusion,
                  'spare_witness': spare_witness, **metrics}
        data['metrics'] = metrics
        (args.out / (data['name'] + '.json')).write_text(json.dumps(data, indent=2) + '\n')
        (args.out / (data['name'] + '.bits')).write_text(bits + '\n')
        (args.out / (data['name'] + '.equations')).write_text('\n'.join(
            f'{i:02}: {base.pretty(a)} = {base.pretty(b)}'
            for i, (a,b) in enumerate(data['equations'])) + '\n')
        report['variants'].append(record)
    (args.out / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Assertions must be enabled; omit -O.')
    main()
