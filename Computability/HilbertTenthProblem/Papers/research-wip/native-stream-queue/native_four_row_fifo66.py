"""Exact four-row selectors58, raw FIFO66, and centered carry71.

Rows are 0->0, 0->1, 1->2, 2->0.  Finite-state universality of a
separately coded machine does not make its controller arithmetic free.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path

import sympy as sp
import input_bridge_boolean_ternary60 as raw

ROWS = ((0, 0), (0, 1), (1, 2), (2, 0))
PREFIX = [('group', '+', 'F1', 'F2'), ('partial_H', '+', 'F0', 'group'),
          ('Hrep', '+', 'partial_H', 'F3'), ('twice_H', '+', 'Hrep', 'Hrep'),
          ('q_calc', '+', 'twice_H', 1)]
PACK = []
previous = 'group'
for j in reversed(range(4)):
    PACK += [(f'pack_mul{j}', '*', 'q', previous),
             (f'pack_sum{j}', '+', f'F{j}', f'pack_mul{j}')]
    previous = f'pack_sum{j}'
FIFO = [('append', '+', 'group', 'F2'), ('twice_F3', '+', 'F3', 'F3'),
        ('read', '+', 'F2', 'twice_F3'), ('initial', '+', 'x', 'x'),
        ('tail', '*', 'W', 'append'), ('transport', '+', 'initial', 'tail'),
        ('width', '+', 'initial', 'width_beta'), ('geometry', '*', 'W', 'L')]
CONTROL = [('weight1', '*', 'a1', 'F1'), ('weight2', '*', 'a2', 'F2'),
           ('weight3', '*', 'a3', 'F3'), ('sum12', '+', 'weight1', 'weight2'),
           ('control', '+', 'sum12', 'weight3')]


def source(fifo, control=False):
    assert fifo or not control
    parameters = ['q', 'F0', 'F1', 'F2', 'F3']+(['x', 'W'] if fifo else [])
    auxiliaries = raw.prior.CORE_NAMES+['bound_beta']+(['width_beta', 'L'] if fifo else [])
    constants = ['a1', 'a2', 'a3', 'gap'] if control else []
    z = {name: sp.Symbol(name) for name in parameters+auxiliaries+constants}
    schedule = PREFIX+PACK+raw.CORE+[('X_bound', '+', 'r', 'bound_beta')]
    equalities = [('r', 'pack_sum0')]+raw.prior.kernel.EQUALITIES[1:]
    equalities += [('X_bound', 'wn2'), ('q_calc', 'q')]
    q = z['q']; fields = [z[f'F{i}'] for i in range(4)]
    polynomials = [z['r']-sum(F*q**j for j, F in enumerate(fields))
                   -(fields[1]+fields[2])*q**4]
    polynomials += raw.independent_sources(dict(z, alpha=0), False)[1:11]
    polynomials += [z['r']+z['bound_beta']-z['w']*q, 2*sum(fields)+1-q]
    if fifo:
        schedule += FIFO
        equalities += [('read', 'transport'), ('width', 'W'), ('geometry', 'q')]
        polynomials += [fields[2]+2*fields[3]-2*z['x']-z['W']*(fields[1]+2*fields[2]),
                        2*z['x']+z['width_beta']-z['W'], z['W']*z['L']-q]
    if control:
        schedule += CONTROL
        equalities += [('control', 'gap')]
        polynomials += [sum(z[f'a{i}']*fields[i] for i in (1, 2, 3))-z['gap']]
    env = raw.prior.execute(schedule, dict(z, n2=q))
    u = 2*z['r']+1+z['j']*z['c']
    correction = polynomials[8]*(u*u-z['y_aux']**2)
    records = []
    assert len(equalities) == len(polynomials)
    for index, ((left, right), polynomial) in enumerate(zip(equalities, polynomials)):
        adjust = correction if index == 9 else 0
        assert sp.expand(env[left]-env[right]-polynomial-adjust) == 0, index
        records.append(dict(equality=[left, right], polynomial=str(sp.expand(polynomial)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(op for _, op, _, _ in schedule)
    expected = 58+8*fifo+5*control
    assert len(schedule) == expected
    assert counts['*'] == 29+2*fifo+3*control
    assert set().union(*(p.free_symbols for p in polynomials)) == set(z.values())
    return dict(operations=expected, multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'],
                parameters=parameters, positive_auxiliaries=auxiliaries,
                witnesses_excluding_x=len(parameters)+len(auxiliaries)-int(fifo),
                fixed_constants=constants, equations=len(equalities),
                schedule=schedule, sources=records)


def word(digits):
    return sum(int(d)*3**j for j, d in enumerate(digits))


def digit_planes(initial, m):
    digits = [initial//3**j % 3 for j in range(m)]
    return word(d == 1 for d in digits), word(d == 2 for d in digits)


def selectors():
    checked = admitted = 0
    for t in range(1, 5):
        q = 3**t; H = (q-1)//2
        for F0 in range(1, H-2):
            for F1 in range(1, H-F0-1):
                for F2 in range(1, H-F0-F1):
                    F3 = H-F0-F1-F2
                    fields = (F0, F1, F2, F3); group = F1+F2
                    r = raw.pack((*fields, group), q)
                    arithmetic = raw.prior.valuation(r) == 0 and r % 2 == 0
                    one_hot = all(sum(F//3**j % 3 for F in fields) == 1
                                  for j in range(t))
                    semantic = (all(raw.native_boolean(F, t) for F in fields)
                                and one_hot and (H+group) % 2 == 0)
                    assert arithmetic == semantic
                    assert all(0 < F < q for F in (*fields, group))
                    checked += 1; admitted += arithmetic
    return dict(arbitrary_positive_checksum_tuples=checked, admitted=admitted)


def physical(initial, m, labels):
    queue = initial; W = 3**m
    for label in labels:
        read, append = ROWS[label]
        if queue % 3 != read:
            return False
        queue = queue//3+(W//3)*append
    return queue == 0


def fifo_checks():
    checked = accepted = 0; examples = []
    for t in range(4, 8):
        q = 3**t
        for labels in product(range(4), repeat=t):
            if len(set(labels)) != 4:
                continue
            fields = [word(label == i for label in labels) for i in range(4)]
            A, D = fields[1]+2*fields[2], fields[2]+2*fields[3]
            group = fields[1]+fields[2]
            for m in range(1, min(t, 4)+1):
                W = 3**m
                # Include arbitrary supplied ordinary inputs, rather than
                # only an input back-solved from a successful transport.
                for x in range(1, min(5, (W-1)//2)+1):
                    arithmetic = (D == 2*x+W*A and t % 2 == 0)
                    semantic = physical(2*x, m, labels) and t % 2 == 0
                    assert arithmetic == semantic
                    checked += 1
                    if not arithmetic:
                        continue
                    I1, I2 = digit_planes(2*x, m)
                    assert fields[2] == I1+W*fields[1]
                    assert fields[3] == I2+W*fields[2]
                    assert group % 2 == 0
                    assert raw.pack((*fields, group), q) % 2 == 0
                    accepted += 1
                    if len(examples) < 3:
                        examples.append(dict(x=x, m=m, t=t, labels=labels, fields=fields))
    return dict(arbitrary_input_label_width_cases=checked, accepted=accepted, examples=examples)


def erasing_run(x):
    initial = 2*x; m = 2
    while 3**(m-1) <= initial:
        m += 2
    W = 3**m; queue = initial; labels = []
    # A single fresh high zero emits a pulse. Its next two visits use
    # 1->2 and2->0; every other zero stays zero throughout three sweeps.
    for time in range(3*m):
        d = queue % 3
        label = 1 if time == m-1 else (0 if d == 0 else 2 if d == 1 else 3)
        read, append = ROWS[label]
        assert d == read
        queue = queue//3+(W//3)*append
        labels.append(label)
    assert queue == 0 and set(labels) == set(range(4))
    return m, labels


def positive_maps():
    examples = []
    for x in range(1, 201):
        m, labels = erasing_run(x); t = len(labels); W = 3**m; q = 3**t
        fields = [word(label == i for label in labels) for i in range(4)]
        A, D = fields[1]+2*fields[2], fields[2]+2*fields[3]
        assert t % 2 == 0 and physical(2*x, m, labels)
        assert D == 2*x+W*A and 2*x < W and q == W**3
        assert all(F > 0 for F in fields)
        r = raw.pack((*fields, fields[1]+fields[2]), q)
        assert r % 2 == 0 and raw.prior.valuation(r) == 0
        if x in (1, 2, 10, 200):
            examples.append(dict(x=x, m=m, t=t, fields=fields,
                                 width_beta=W-2*x, L=q//W))
    return dict(ordinary_inputs=200, examples=examples,
                kernel_witnesses='Parametric strong raw-kernel extension; not materialized')


def carry_checks():
    checked = 0
    for t in range(1, 6):
        for labels in product(range(4), repeat=t):
            F = [word(label == i for label in labels) for i in range(4)]
            for coefficients, gap in (((1, -2, 3), 4), ((-3, 5, 0), -1),
                                      ((0, 0, 0), 0), ((2, 0, -1), 2)):
                arithmetic = sum(a*F[i] for a, i in zip(coefficients, (1, 2, 3))) == gap
                state = -gap; integral = True
                for label in labels:
                    numerator = state+(0 if label == 0 else coefficients[label-1])
                    if numerator % 3:
                        integral = False; break
                    state = numerator//3
                assert arithmetic == (integral and state == 0)
                checked += 1
    return dict(word_controller_cases=checked,
                scope='Exact centered integral carry projection, not arbitrary finite control')


def verify():
    return dict(status='PASS_FOUR_ROW_SELECTORS58_FIFO66_CARRY71',
                sources={str(58+8*fifo+5*control): source(fifo, control)
                         for fifo, control in ((False, False), (True, False), (True, True))},
                selectors=selectors(), fifo=fifo_checks(), positive=positive_maps(),
                centered_carry=carry_checks(),
                limits='The66 source has a universal erasing witness for every positive input, '
                       'not a universal accepting controller. The71 centered carry family '
                       'cannot be a universal representation family; see the proof. '
                       'The complete bound remains75.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true')
    args = parser.parse_args(); result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'], {k: (v['multiplications'], v['additions_subtractions'], v['equations'])
                            for k, v in result['sources'].items()},
          result['selectors'], result['fifo']['arbitrary_input_label_width_cases'])
