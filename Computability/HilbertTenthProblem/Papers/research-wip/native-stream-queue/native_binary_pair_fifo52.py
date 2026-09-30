"""Exact paired binary FIFO52; affine controller61 is not a universal compiler."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path

import sympy as sp
import pell_kernel_power_two43 as geometry

PARAMETERS = ['x', 'K', 'W', 'q', 'read0', 'read1', 'append0', 'append1']
EXTRA_AUX = ['L', 'beta', 'alpha0', 'alpha1']
FIFO = [('queue_width', '*', 2, 'K'),
        ('input_bound', '+', 'x', 'beta'),
        ('total_time', '*', 'W', 'L'),
        ('appended0', '*', 'W', 'append0'),
        ('transport0', '+', 'x', 'appended0'),
        ('appended1', '*', 'W', 'append1'),
        ('transport1', '+', 'K', 'appended1'),
        ('read_bound0', '+', 'read0', 'alpha0'),
        ('read_bound1', '+', 'read1', 'alpha1')]
FIFO_EQ = [('W', 'queue_width'), ('K', 'input_bound'), ('q', 'total_time'),
           ('read0', 'transport0'), ('read1', 'transport1'),
           ('read_bound0', 'q'), ('read_bound1', 'q')]


def execute(rows, inputs):
    env = dict(inputs)
    for name, op, left, right in rows:
        assert name not in env, name
        a = env[left] if isinstance(left, str) else left
        b = env[right] if isinstance(right, str) else right
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def source_check():
    auxiliaries = geometry.prior.CORE_NAMES + EXTRA_AUX
    z = {name: sp.Symbol(name) for name in PARAMETERS+auxiliaries}
    schedule = geometry.SCHEDULE + FIFO
    env = execute(schedule, z)
    sources = geometry.sources(z) + [z['W']-2*z['K'], z['K']-z['x']-z['beta'],
        z['q']-z['W']*z['L'], z['read0']-z['x']-z['W']*z['append0'],
        z['read1']-z['K']-z['W']*z['append1'],
        z['read0']+z['alpha0']-z['q'], z['read1']+z['alpha1']-z['q']]
    equations = geometry.EQUALITIES + FIFO_EQ
    U = z['j']*z['c']-(2*z['r']+1)
    correction = sources[8]*(U*U-z['y_aux']**2)
    records = []
    for ix, ((left, right), source) in enumerate(zip(equations, sources)):
        adjust = correction if ix == 9 else 0
        actual = env[left]-env[right]
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, ix
        records.append(dict(equality=[left, right], source=str(sp.expand(source)),
                            source_sign=sign, correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 52 and counts['*'] == 29
    assert counts['+']+counts['-'] == 23
    assert len(equations) == len(sources) == 18 and len(auxiliaries) == 21
    assert set().union(*(p.free_symbols for p in sources)) == set(z.values())
    return dict(operations=52, multiplications=29, additions_subtractions=23, equations=18,
                positive_parameters=PARAMETERS, positive_auxiliaries=auxiliaries,
                positive_witnesses_excluding_x=28, instructions=[list(row) for row in schedule],
                sources=records)


def direct_fifo(initial, width, reads, appends):
    queues = list(initial)
    for read, append in zip(reads, appends):
        if any(queues[i] % 2 != read[i] for i in (0, 1)):
            return False
        queues = [queues[i]//2+(width//2)*append[i] for i in (0, 1)]
        assert all(0 <= n < width for n in queues)
    return queues == [0, 0]


def exhaustive():
    cases = accepted = 0
    for t in range(3, 5):
        q = 2**t
        for m in range(2, t+1):
            W, K = 2**m, 2**(m-1)
            for x in range(1, K):
                for read0, read1, app0, app1 in product(range(1, q), repeat=4):
                    reads = [(read0//2**j % 2, read1//2**j % 2) for j in range(t)]
                    appends = [(app0//2**j % 2, app1//2**j % 2) for j in range(t)]
                    arithmetic = read0 == x+W*app0 and read1 == K+W*app1
                    semantic = direct_fifo((x, K), W, reads, appends)
                    assert arithmetic == semantic
                    if arithmetic:
                        assert t >= m+1 and app0 < q and app1 < q
                        accepted += 1
                    cases += 1
    return dict(arbitrary_positive_stream_tuples=cases, accepted=accepted, maximum_t=4)


def all_inputs():
    rows = []
    for x in range(1, 201):
        K = 2
        while K <= x:
            K *= 2
        W, q = 2*K, 4*K
        m = W.bit_length()-1
        t = m+1
        values = dict(x=x, K=K, W=W, q=q, r=q-1, read0=x+W, read1=K+W,
                      append0=1, append1=1, L=2, beta=K-x,
                      alpha0=W-x, alpha1=K)
        assert min(values.values()) > 0
        env = execute(FIFO, values)
        assert all(env[left] == env[right] for left, right in FIFO_EQ)
        reads = [(values['read0']//2**j % 2, values['read1']//2**j % 2) for j in range(t)]
        appends = [(int(j == 0), int(j == 0)) for j in range(t)]
        assert direct_fifo((x, K), W, reads, appends)
        if x <= 3:
            rows.append(values)
    return dict(ordinary_positive_inputs=200, canonical_positive_outer_maps=200,
                first_examples=rows, kernel_extension='Exact power43 positive converse; auxiliary tuple not materialized')


def controller_schedules(source):
    words = ['read0', 'read1', 'append0', 'append1']
    products = [(f'binary_control_p{i}', '*', f'weight{i}', word) for i, word in enumerate(words)]
    sums = [('binary_control_s01', '+', 'binary_control_p0', 'binary_control_p1'),
            ('binary_control_s012', '+', 'binary_control_s01', 'binary_control_p2'),
            ('binary_control_s0123', '+', 'binary_control_s012', 'binary_control_p3')]
    extra = products+sums+[('binary_control_q', '*', 'q_coefficient', 'q'),
                           ('binary_control_left', '+', 'binary_control_s0123', 'binary_control_q')]
    z = {name: sp.Symbol(name) for name in source['positive_parameters']+source['positive_auxiliaries']+
         [f'weight{i}' for i in range(4)]+['q_coefficient', 'comparison_constant']}
    env = execute(source['instructions']+extra, z)
    raw = sum(z[f'weight{i}']*z[word] for i, word in enumerate(words))
    expected = raw+z['q_coefficient']*z['q']-z['comparison_constant']
    assert sp.expand(env['binary_control_left']-z['comparison_constant']-expected) == 0
    assert len(extra) == 9
    h, cs, cf = sp.symbols('h cs cf')
    global_carry = raw+h*(z['q']-1)+cs-z['q']*cf
    assert sp.expand(expected.subs({z['q_coefficient']: h-cf,
                                   z['comparison_constant']: h-cs})-global_carry) == 0
    return dict(operations=61, multiplications=34, additions_subtractions=27, equations=19,
                extra_instructions=[list(row) for row in extra], equality=['binary_control_left', 'comparison_constant'],
                fixed_constants='q_coefficient=h-cf; comparison_constant=h-cs',
                local_relation='2*c_next=c+h+c0*d0+c1*d1+c2*a0+c3*a1',
                scope='Entire unfiltered binary carry graph coupled to the paired FIFO; universality not established')


def carry_examples():
    checked = 0
    for weights in product(range(-1, 2), repeat=4):
        for h, cs in product(range(-1, 2), repeat=2):
            for labels in product(tuple(product((0, 1), repeat=4)), repeat=2):
                words = [labels[0][i]+2*labels[1][i] for i in range(4)]
                value = cs+3*h+sum(c*f for c, f in zip(weights, words))
                integral = value % 4 == 0
                carry = cs
                local = True
                for label in labels:
                    numerator = carry+h+sum(c*b for c, b in zip(weights, label))
                    if numerator % 2:
                        local = False
                        break
                    carry = numerator//2
                assert integral == local
                if local:
                    assert 4*carry == value
                checked += 1
    return dict(two_step_global_local_checks=checked)


def verify():
    source = source_check()
    return dict(status='PASS_COMPLETE_NATIVE_BINARY_PAIR_FIFO_52', source=source,
                exhaustive=exhaustive(), all_inputs=all_inputs(),
                controller=controller_schedules(source), carry_examples=carry_examples(),
                geometry_source_sha256=hashlib.sha256(Path(geometry.__file__).read_bytes().replace(b'\r\n', b'\n')).hexdigest(),
                scope='Exact positive paired binary FIFO with marker input; no universal controller supplied',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(json.dumps({key: value for key, value in result.items() if key != 'source'}, indent=2))
