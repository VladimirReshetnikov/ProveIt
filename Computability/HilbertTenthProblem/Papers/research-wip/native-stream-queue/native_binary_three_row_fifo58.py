"""Exact three-selector53 and binary FIFO58 with ordinary input2x.

The physical rows are00,01,10.  A finite universal controller and an
ordinary-source-input loader are separate from this component theorem.
"""
import argparse
from collections import Counter
from itertools import product
import json
from math import comb
from pathlib import Path
import random

import sympy as sp

import native_controller_binary_selector56 as prior


CORE = list(prior.CORE)
CORE_NAMES = list(prior.CORE_NAMES)
OUTER = [('bs_p2', '*', 'q', 'F2'), ('bs_p3', '+', 'F1', 'bs_p2'),
         ('bs_p4', '*', 'q', 'bs_p3'), ('bs_packed', '+', 'F0', 'bs_p4'),
         ('bs_sum01', '+', 'F0', 'F1'), ('bs_sum012', '+', 'bs_sum01', 'F2'),
         ('bs_q', '+', 'bs_sum012', 1),
         ('bs_even', '*', 2, 'odd_half'), ('bs_odd', '+', 'bs_even', 1)]
BOUND = [('bs_X_bound', '+', 'r', 'bound_beta')]
FIFO = [('fifo_input', '+', 'x', 'x'),
        ('fifo_width', '+', 'fifo_input', 'width_beta'),
        ('fifo_time', '*', 'W', 'L'),
        ('fifo_append', '*', 'W', 'F1'),
        ('fifo_read', '+', 'fifo_input', 'fifo_append')]
CONTROLLER = [('ctrl_first', '*', 'ctrl_a', 'F1'),
              ('ctrl_second', '*', 'ctrl_b', 'F2'),
              ('ctrl_sum', '+', 'ctrl_first', 'ctrl_second')]


def source_check(fifo=False, centered=False, nonabsorbing=False):
    assert not centered or fifo
    assert not nonabsorbing or centered
    parameters = ['x'] if fifo else ['q', 'F0', 'F1', 'F2']
    auxiliaries = ((['q', 'F0', 'F1', 'F2'] if fifo else [])
                   +CORE_NAMES+['odd_half', 'bound_beta']
                   +(['W', 'L', 'width_beta'] if fifo else []))
    constants = (['ctrl_a', 'ctrl_b', 'ctrl_g']+(['ctrl_c'] if nonabsorbing else [])) if centered else []
    z = {name: sp.Symbol(name) for name in parameters+auxiliaries+constants}
    schedule = OUTER+CORE+BOUND+(FIFO if fifo else [])+(CONTROLLER if centered else [])
    if nonabsorbing:
        schedule += [('ctrl_time', '*', 'ctrl_c', 'q'),
                     ('ctrl_full_sum', '+', 'ctrl_sum', 'ctrl_time')]
    env = prior.ternary.execute(schedule, dict(z, n2=z['q']))
    equalities = [('r', 'bs_packed'), ('bs_q', 'q'), ('s', 'bs_odd'),
                  ('bs_X_bound', 'wn2')]+prior.CORE_EQUALITIES
    polynomials = prior.independent_sources(dict(z, F3=sp.Integer(0)))
    if fifo:
        equalities += [('fifo_width', 'W'), ('fifo_time', 'q'), ('fifo_read', 'F2')]
        polynomials += [2*z['x']+z['width_beta']-z['W'],
                        z['W']*z['L']-z['q'],
                        2*z['x']+z['W']*z['F1']-z['F2']]
    if centered:
        equalities.append(('ctrl_full_sum' if nonabsorbing else 'ctrl_sum', 'ctrl_g'))
        polynomials.append(z['ctrl_a']*z['F1']+z['ctrl_b']*z['F2']-z['ctrl_g']
                           +(z['ctrl_c']*z['q'] if nonabsorbing else 0))
    U = z['j']*z['c']-(2*z['r']+1)
    correction = polynomials[11]*(U*U-z['y_aux']**2)
    records = []
    for index, ((left, right), polynomial) in enumerate(zip(equalities, polynomials)):
        adjust = correction if index == 12 else 0
        assert sp.expand(env[left]-env[right]-polynomial-adjust) == 0, index
        records.append(dict(equality=[left, right], source=sp.sstr(sp.expand(polynomial)),
                            correction=sp.sstr(sp.expand(adjust))))
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in schedule)
    expected = ((63, 33, 30) if nonabsorbing else (61, 32, 29)) if centered else (58, 30, 28) if fifo else (53, 28, 25)
    assert (len(schedule), counts['M'], counts['A']) == expected
    assert len(equalities) == 14+3*fifo+centered
    assert len(auxiliaries) == (26 if fifo else 19)
    assert set().union(*(p.free_symbols for p in polynomials)) == set(z.values())
    assert CORE == prior.retained.CORE
    return dict(operations=expected[0], multiplications=expected[1], additions_subtractions=expected[2],
                equations=len(equalities), positive_parameters=parameters,
                positive_auxiliaries=auxiliaries, fixed_integer_coefficients=constants,
                aliases={'n2': 'q', 'read_stream': 'F2', 'append_stream': 'F1'},
                schedule=[list(row) for row in schedule], sources=records)


def pack(q, fields):
    return fields[0]+q*fields[1]+q*q*fields[2]


def bootstrap():
    cases = 0
    for q in range(4, 41):
        for F0 in range(1, q-2):
            for F1 in range(1, q-1-F0):
                F2 = q-1-F0-F1
                assert F2 >= 1
                r = pack(q, (F0, F1, F2))
                X, Y = q*(r//q+1), 3*q
                E, a = X*Y, Y*(X+1)
                A, P = a+2, 2*X*Y*Y+1
                assert q*q+q+1 <= r < q**3 and r >= 21
                assert X > r and E > r+1 and a > 2*r+1
                assert P > A and 6*X*Y*Y > a
                assert Y*(r+1) > 2*(2*r+1)
                assert r+2 >= 23
                assert (2*A-1)**5 > A*(A*A-1)**2
                cases += 1
    for r in range(21, 501):
        assert (r+1)**3 > 12*r
        assert 48*r < 2**(2*r+1)+1
    return dict(positive_checksum_tuples=cases, q_range=[4, 40], minimum_r=21,
                minimum_preliminary_main_index=23, postpower_smallest_q=8,
                scope='Pre-power inequalities are checked before interpreting any field as a word')


def selector_checks():
    scanned = admitted = 0
    for t in range(2, 8):
        q = 2**t
        for F0 in range(1, q-2):
            for F1 in range(1, q-1-F0):
                F2 = q-1-F0-F1
                fields = F0, F1, F2
                r = pack(q, fields)
                onehot = all(sum(F >> j & 1 for F in fields) == 1 for j in range(t))
                assert (r.bit_count() == t) == onehot
                assert (r % 2) == (F0 % 2)
                accepted = onehot and bool(F0 % 2)
                if accepted:
                    assert t >= 3 and q >= 8
                    assert F1 % 2 == F2 % 2 == 0
                    assert F1 & F2 == 0
                    admitted += 1
                scanned += 1
    prototypes = []
    for q, fields in ((8, (1, 2, 4)), (8, (1, 4, 2)), (16, (5, 2, 8))):
        r = pack(q, fields)
        central = comb(2*r, r)
        valuation = (central & -central).bit_length()-1
        assert valuation == r.bit_count() == q.bit_length()-1
        assert central//q % 2 == 1
        prototypes.append(dict(q=q, fields=fields, r=r, central_valuation=valuation,
                               central_bits=central.bit_length()))
    return dict(checksum_tuples=scanned, exact_origin_partitions=admitted,
                valuation_prototypes=prototypes)


def run_fifo(initial, W, append, t):
    state, read, labels = initial, 0, []
    for j in range(t):
        assert 0 <= state < W
        digit, bit = state % 2, append >> j & 1
        read += digit << j
        labels.append((digit, bit))
        state = state//2+(W//2)*bit
    return state, read, labels


def fifo_checks():
    cases = accepted = 0
    for t in range(3, 9):
        q = 2**t
        for m in range(2, t):
            W = 2**m
            for x in range(1, W//2):
                initial = 2*x
                for append in range(1, (q-1-initial)//W+1):
                    read = initial+W*append
                    final, actual_read, labels = run_fifo(initial, W, append, t)
                    assert final == 0 and actual_read == read
                    allowed = labels[0] == (0, 0) and all(row != (1, 1) for row in labels)
                    expected = append % 2 == 0 and append & read == 0
                    assert allowed == expected
                    F0 = q-1-append-read
                    typed = (F0 > 0 and F0 % 2 == 1
                             and pack(q, (F0, append, read)).bit_count() == t)
                    assert typed == allowed
                    if typed:
                        assert set(labels) == {(0, 0), (0, 1), (1, 0)}
                        accepted += 1
                    cases += 1
    for x in range(1, 301):
        W = 1 << (2*x).bit_length()
        m = W.bit_length()-1
        t, q, append, read = 2*m+1, 2*W*W, W, 2*x+W*W
        F0 = q-1-append-read
        assert W > 2*x and m >= 2 and min(F0, append, read) > 0
        assert F0 % 2 == 1 and append & read == 0
        assert pack(q, (F0, append, read)).bit_count() == t
        final, actual_read, labels = run_fifo(2*x, W, append, t)
        assert final == 0 and actual_read == read
        assert labels[0] == (0, 0) and set(labels) == {(0, 0), (0, 1), (1, 0)}
    return dict(arbitrary_bounded_stream_cases=cases, admitted_three_row_runs=accepted,
                ordinary_positive_inputs_covered=300,
                all_input_construction='W=least 2-power>2x, A=W, D=2x+W^2, q=2W^2, t=2log2(W)+1')


def centered_decide(x, a, b, g):
    I = 2*x
    if b == 0:
        if a == 0:
            return g == 0
        if g % a:
            return False
        A = g//a
        return A > 0 and A % 2 == 0 and A & I == 0
    if abs(b)*I > max(abs(a), abs(g)):
        return False
    N = g-b*I
    W = 4
    bound = (abs(a)+abs(N))//abs(b)
    while W <= bound:
        if W > I:
            denominator = a+b*W
            if denominator == 0:
                if N == 0:
                    return True  # The ordinary bare-component construction at this W.
            elif N % denominator == 0:
                A = N//denominator
                if A > 0 and A % 2 == 0 and A & (I+W*A) == 0:
                    return True
        W *= 2
    return False


def centered_checks():
    rng = random.Random(5861)
    triples = [(0, 0, 0), (0, 0, 1), (1, 0, 2), (1, 0, 4),
               (-10, 1, -6), (-8, 1, 4)]
    triples += [(rng.randint(-20, 20), rng.randint(-3, 3), rng.randint(-40, 40))
                for _ in range(160)]
    checked = admitted = 0
    for a, b, g in triples:
        for x in range(1, 21):
            actual = False
            for m in range(2, 13):
                W = 2**m
                if W <= 2*x:
                    continue
                for A in range(2, 201, 2):
                    D = 2*x+W*A
                    if A & D == 0 and a*A+b*D == g:
                        actual = True
                        break
                if actual:
                    break
            expected = centered_decide(x, a, b, g)
            assert actual == expected, (x, a, b, g)
            if expected and b:
                assert 2*abs(b)*x <= max(abs(a), abs(g))
            checked += 1
            admitted += expected
    return dict(classification_cases=checked, admitted=admitted,
                finite_case_input_bound='2*abs(b)*x <= max(abs(a),abs(g)) when b!=0',
                unbounded_case='When b=0 and g/a is positive even, acceptance is exactly (2x)&(g/a)=0',
                scope='Centered fixed affine relation only; no q term or general finite controller')


def nonabsorbing_checks():
    cases = 0
    rows = ((0, 0), (0, 1), (1, 0))
    for t in range(3, 6):
        q = 2**t
        for tail in product(range(3), repeat=t-1):
            labels = (0,)+tail
            if set(labels) != {0, 1, 2}:
                continue
            A = sum(1 << j for j, label in enumerate(labels) if label == 1)
            D = sum(1 << j for j, label in enumerate(labels) if label == 2)
            for a, b in product(range(-2, 3), repeat=2):
                for g, c in product(range(-4, 5), range(-3, 4)):
                    state, integral = -g, True
                    for label in labels:
                        d, append = rows[label]
                        numerator = state+a*append+b*d
                        if numerator % 2:
                            integral = False
                            break
                        state = numerator//2
                        assert abs(state) <= max(abs(g), abs(a), abs(b))
                    assert (a*A+b*D+c*q == g) == (integral and state == -c)
                    cases += 1
    # An actual FIFO58 outer tuple with a nonzero terminal carry.  A final
    # 00 step preserves the queue endpoint but violates this controller.
    x, W, A, D, q = 1, 4, 4, 18, 32
    a, b, c, g = 0, 1, 1, 50
    assert D == 2*x+W*A and A & D == 0 and A % 2 == 0
    assert q-1-A-D > 0 and (q-1-A-D) % 2 == 1
    assert a*A+b*D+c*q == g and a*A+b*D+c*(2*q) != g
    return dict(exact_global_local_cases=cases,
                no_free_zero_padding_example=dict(x=x, W=W, A=A, D=D, q=q,
                                                  a=a, b=b, c=c, g=g),
                scope='Paid affine carry with initial -g and final -c; no universality or centered-collapse claim')


def verify():
    return dict(status='PASS_NATIVE_BINARY_THREE_ROW_FIFO58',
                selector_source=source_check(), fifo_source=source_check(True),
                centered_source=source_check(True, True), bootstrap=bootstrap(),
                nonabsorbing_source=source_check(True, True, True),
                selectors=selector_checks(), fifo=fifo_checks(), centered=centered_checks(),
                nonabsorbing=nonabsorbing_checks(),
                projection='q=2^t,W=2^m,2x<W,t>m; exact t-step fixed-width binary FIFO from2x to0, rows00/01/10 only, first00, all three rows occur',
                established_complete_universal_bound=75,
                limits='Complete positive finite FIFO component with all ordinary input coverage; generic finite controller and original-source-input block loader remain unpaid; not a new universal certificate')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(result['status'], 'selector53=28M+25A; FIFO58=30M+28A; centered61=32M+29A')
