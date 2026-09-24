#!/usr/bin/env python3
"""Primary table transcription and a conditional Boolean lookup compiler.

No finite-configuration universality claim is made. The finite tests validate
the two stated case rules and an unoptimized packed arithmetic relation.
"""
from itertools import product
from pathlib import Path
from collections import Counter
import json

BBM = [0, 8, 4, 3, 2, 5, 9, 7, 1, 6, 10, 11, 12, 13, 14, 15]
CRITTERS = [15, 14, 13, 3, 11, 5, 6, 1, 7, 9, 10, 2, 12, 4, 8, 0]
RADIX = 4096


def rotate(x):
    # Clockwise: NW -> NE -> SE -> SW -> NW.
    return ((x & 1) << 1) | ((x & 2) << 2) | ((x & 8) >> 1) | ((x & 4) >> 2)


def cases_bbm(x):
    if x.bit_count() == 1:
        return rotate(rotate(x))
    if x in (6, 9):
        return x ^ 15
    return x


def cases_critters(x):
    weight = x.bit_count()
    if weight == 2:
        return x
    if weight == 3:
        return rotate(rotate(x ^ 15))
    return x ^ 15


def schedule(table):
    statements = []

    def linear(label, terms):
        terms = [(coefficient, variable) for coefficient, variable in terms if coefficient]
        registers = []
        for index, (coefficient, variable) in enumerate(terms):
            if coefficient == 1:
                registers.append(variable)
            else:
                target = f'{label}_m{index}'
                statements.append((target, '*', coefficient, variable))
                registers.append(target)
        result = registers[0]
        for index, register in enumerate(registers[1:], 1):
            target = f'{label}_a{index}'
            statements.append((target, '+', result, register))
            result = target
        return result

    fields = ['a', 'b', 'c', 'd', 'ap', 'bp', 'cp', 'dp']
    left = linear('state', [(2**i, field) for i, field in enumerate(fields)])
    right = linear('lookup', [(k + 16 * table[k], f'E{k}') for k in range(16)])
    selector = linear('selector', [(1, f'E{k}') for k in range(16)])
    return statements, [(left, right), (selector, 'J')]


def evaluate(statements, inputs):
    registers = dict(inputs)
    for target, op, left, right in statements:
        assert target not in registers
        lv = registers[left] if isinstance(left, str) else left
        rv = registers[right] if isinstance(right, str) else right
        assert op in ('+', '*')
        registers[target] = lv + rv if op == '+' else lv * rv
    return registers


def verify():
    models = {}
    graph_cases = 0
    selector_cases = 0
    for bits in product((0, 1), repeat=16):
        assert (sum(bits) == 1) == (bits.count(1) == 1)
        selector_cases += 1
    for name, table, case_rule in [('BBM', BBM, cases_bbm), ('Critters', CRITTERS, cases_critters)]:
        assert table == [case_rule(x) for x in range(16)]
        assert sorted(table) == list(range(16))
        assert all(table[rotate(x)] == rotate(table[x]) for x in range(16))
        if name == 'BBM':
            assert all(table[table[x]] == x for x in range(16))
            assert all(table[x].bit_count() == x.bit_count() for x in range(16))
        else:
            assert any(table[table[x]] != x for x in range(16))
            assert all(table[x].bit_count() == 4 - x.bit_count() for x in range(16))
        for x, y, selector in product(range(16), repeat=3):
            accepted = x + 16 * y == selector + 16 * table[selector]
            assert accepted == (x == selector and y == table[x])
            graph_cases += 1
        statements, equalities = schedule(table)
        histogram = dict(Counter(row[1] for row in statements))
        assert histogram == ({'*': 22, '+': 36} if name == 'BBM' else {'*': 23, '+': 37})
        assert sum(k + 16 * table[k] for k in range(16)) == 2040 < RADIX
        # Pack all 16 valid transitions simultaneously; Booleanity is supplied.
        inputs = {'J': sum(RADIX**k for k in range(16))}
        for index, field in enumerate(['a', 'b', 'c', 'd']):
            inputs[field] = sum(((k >> index) & 1) * RADIX**k for k in range(16))
        for index, field in enumerate(['ap', 'bp', 'cp', 'dp']):
            inputs[field] = sum(((table[k] >> index) & 1) * RADIX**k for k in range(16))
        inputs.update({f'E{k}': RADIX**k for k in range(16)})
        registers = evaluate(statements, inputs)
        assert all(registers[left] == registers[right] for left, right in equalities)
        models[name] = {'table': table, 'primitive_count': len(statements), 'histogram': histogram,
                        'statements': statements, 'equalities': equalities}
    return {'status': 'PASS_CONDITIONAL_LOCAL_RELATIONS_ONLY',
            'scope': 'Exact table and arithmetic checks; no strong finite-configuration universality result.',
            'radix': RADIX, 'one_hot_vectors_checked': selector_cases,
            'graph_triples_checked': graph_cases, 'packed_transitions_checked': 32,
            'sources': ['https://fab.cba.mit.edu/classes/862.22/notes/computation/Margolus-1984.pdf',
                        'https://arxiv.org/pdf/comp-gas/9811002'],
            'models': models}


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({key: value for key, value in receipt.items() if key != 'models'}, indent=2))
    print('BBM 58 primitives; Critters 60 primitives. Universality interface remains unproved.')
