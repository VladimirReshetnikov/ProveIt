#!/usr/bin/env python3
"""Exact counts for a conditional 43-operation Pell kernel and one root shift."""
from collections import Counter
import json
from pathlib import Path
import sympy as sp

import round37_1980_binary_product_certificate as published


def evaluate(rows, inputs):
    env = dict(inputs)
    for name, op, left, right in rows:
        a = env[left] if isinstance(left, str) else sp.Integer(left)
        b = env[right] if isinstance(right, str) else sp.Integer(right)
        assert name not in env
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def verify():
    retained = [row for row in published.SCHEDULE[33:77] if row[0] != 'R13']
    assert len(retained) == 43
    assert Counter(row[1] for row in retained) == {'*':25, '+':15, '-':3}
    names = {operand for row in retained for operand in (row[2], row[3])
             if isinstance(operand, str)}
    assert 'n' not in names and 'n2' in names
    assert all(name not in names for name in ('q','ka','mu','phi','rho','Delta','Tindex','th'))

    outer = [('Q','*','q','q'),('Q2','*','Q','Q'),('Q4','*','Q2','Q2'),
             ('Lbig','*','Q4','Q4'),('n2','*','Lbig','Q4')]
    q = sp.Symbol('q')
    out = evaluate(outer, {'q':q})
    assert sp.expand(out['Lbig']-q**16) == 0
    assert sp.expand(out['n2']-q**24) == 0

    remove = {'cam2','D1','R14','Ac2','R15','L15'}
    shifted = []
    for row in retained:
        if row[0] in remove:
            continue
        shifted.append(row)
        if row[0] == 'gam':
            shifted.append(('shifted_exponent','+','wn2','gam'))
        if row[0] == 'c2':
            shifted.extend([
                ('shift_ac','*','a','c'),('twice_ac','*',2,'shift_ac'),
                ('shift_partner','+','z','twice_ac'),
                ('shift_norm_left','*','z','shift_partner'),
                ('shift_Mc2','*','a4m5','c2'),
                ('shift_norm_right','+','shift_Mc2',1),
            ])
    assert len(shifted) == 44
    hist = Counter(row[1] for row in shifted)
    assert hist == {'*':26, '+':15, '-':3}
    needed = {operand for row in retained+shifted for operand in (row[2],row[3])
              if isinstance(operand,str)} - {row[0] for row in retained+shifted}
    symbols = {name:sp.Symbol(name) for name in needed}
    old,new = evaluate(retained,symbols),evaluate(shifted,symbols)
    a,c,z = symbols['a'],symbols['c'],symbols['z']
    sub = {symbols['d']:z+a*c}
    assert sp.expand((old['R14']-symbols['d']).subs(sub)
                     -(new['shifted_exponent']-z)) == 0
    assert sp.expand((old['L15']-old['R15']).subs(sub)
                     -(new['shift_norm_left']-new['shift_norm_right'])) == 0
    common = set(old)&set(new)
    assert all(sp.expand(old[name]-new[name]) == 0 for name in common)
    return dict(status='PASS',scope='Conditional Pell-kernel/interface and exact root-shift arithmetic only; no complete universal certificate.',
                retained_operations=43,retained_histogram=dict(Counter(row[1] for row in retained)),
                outer_power_operations=5,outer_power_schedule=outer,
                shifted_root_operations=44,shifted_root_histogram=dict(hist),
                shifted_root_schedule=shifted,polynomial_equivalence=True,
                improvement='One outer multiplication saved by directly constructing Q12; no retained-kernel reduction proved.',
                proof='../1980/EXPLORATION_FIXED_RADIX_PELL_KERNEL.md')


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(receipt['status'], 'kernel43; direct outer powers5; shifted root44')
