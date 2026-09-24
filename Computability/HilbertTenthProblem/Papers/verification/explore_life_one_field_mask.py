#!/usr/bin/env python3
"""Exact local Life mask and conditional 26-operation wrapper; not universal."""
from itertools import product
from pathlib import Path
import json
import random
import sympy as sp


RADIX = 256
FORBIDDEN = 72
WRAPPER_RADIX = 512
LOCAL = [
    ('s14', '*', 14, 'S'),
    ('y8', '*', 8, 'Y'),
    ('u59', '*', 59, 'U'),
    ('j20', '*', 20, 'J'),
    ('v1', '+', 's14', 'B'),
    ('v2', '+', 'v1', 'y8'),
    ('v3', '+', 'v2', 'u59'),
    ('V', '+', 'v3', 'j20'),
]
SHIFTED_LOCAL = [
    ('s28', '*', 28, 'S'),
    ('b2', '*', 2, 'B'),
    ('y16', '*', 16, 'Y'),
    ('u118', '*', 118, 'U'),
    ('j41', '*', 41, 'J'),
    ('v1', '+', 's28', 'b2'),
    ('v2', '+', 'v1', 'y16'),
    ('v3', '+', 'v2', 'u118'),
    ('Vprime', '+', 'v3', 'j41'),
]
WRAPPER = [
    ('q2', '*', 'q', 'q'),
    ('Lambda', '*', 'q2', 'q2'),
    ('D0', '*', 'Lambda', 'q2'),
    ('ones_left', '*', 511, 'J'),
    ('ones_right', '-', 'q', 1),
] + SHIFTED_LOCAL + [
    ('qu', '*', 'q', 'U'),
    ('bu', '+', 'B', 'qu'),
    ('qbu', '*', 'q', 'bu'),
    ('P', '+', 'Vprime', 'qbu'),
    ('q_q2', '+', 'q', 'q2'),
    ('mask_high', '*', 510, 'q_q2'),
    ('mask_sum', '+', 144, 'mask_high'),
    ('M', '*', 'J', 'mask_sum'),
    ('lambda_minus_p', '-', 'Lambda', 'P'),
    ('lambda_minus_1', '-', 'Lambda', 1),
    ('r_product', '*', 'lambda_minus_p', 'lambda_minus_1'),
    ('r', '+', 'r_product', 'M'),
]


def run(schedule, values):
    env = dict(values)
    for name, op, left, right in schedule:
        assert name not in env
        a = env[left] if isinstance(left, str) else left
        b = env[right] if isinstance(right, str) else right
        env[name] = a+b if op == '+' else a-b if op == '-' else a*b
    return env


def histogram(schedule):
    return {'M': sum(op == '*' for _, op, _, _ in schedule),
            'A': sum(op in ('+', '-') for _, op, _, _ in schedule)}


def life(n, b):
    return int(n == 3 or n == 2 and b == 1)


def digit(n, b, y, u):
    return 20+14*(n+b)+b+8*y+59*u


def pack(values, radix=RADIX):
    return sum(x*radix**i for i, x in enumerate(values))


def verify():
    assert len(LOCAL) == 8 and histogram(LOCAL) == {'M': 4, 'A': 4}
    assert len(SHIFTED_LOCAL) == 9 and histogram(SHIFTED_LOCAL) == {'M': 5, 'A': 4}
    assert len(WRAPPER) == 26 and histogram(WRAPPER) == {'M': 14, 'A': 12}
    symbols = {name: sp.Symbol(name) for name in ('q','J','S','B','Y','U')}
    symbolic = run(WRAPPER, symbols)
    q,J,S,B,Y,U = [symbols[x] for x in ('q','J','S','B','Y','U')]
    Vprime = 28*S+2*B+16*Y+118*U+41*J
    P = Vprime+q*(B+q*U)
    M = J*(144+510*(q+q*q))
    formulas = {'Vprime': Vprime, 'P': P, 'M': M, 'Lambda': q**4,
                'D0': q**6, 'r': (q**4-P)*(q**4-1)+M,
                'ones_left': 511*J, 'ones_right': q-1}
    for name, expected in formulas.items():
        assert sp.expand(symbolic[name]-expected) == 0
    table = []
    witness = {}
    all_digits = []
    scalar = 0
    for n, b in product(range(9), range(2)):
        accepted = []
        values = []
        for y, u in product(range(2), repeat=2):
            v = digit(n, b, y, u)
            assert run(LOCAL, dict(S=n+b, B=b, Y=y, U=u, J=1))['V'] == v
            shifted = run(SHIFTED_LOCAL, dict(S=n+b, B=b, Y=y, U=u, J=1))['Vprime']
            assert shifted == 2*v+1 and 41 <= shifted <= 429 < 512
            assert (shifted & 144 == 0) == (v & 72 == 0)
            values.append(v)
            all_digits.append(v)
            scalar += 1
            if v & FORBIDDEN == 0:
                accepted.append([y, u])
        assert len(accepted) == 1 and accepted[0][0] == life(n, b)
        witness[n, b] = accepted[0][1]
        table.append(dict(neighbors=n, center=b, digits_y0u0_y0u1_y1u0_y1u1=values,
                          accepted=accepted[0]))
    assert (min(all_digits), max(all_digits)) == (20, 214)

    neighborhoods = 0
    for bits in product(range(2), repeat=9):
        n, b = sum(bits[:8]), bits[8]
        for y, u in product(range(2), repeat=2):
            assert (digit(n, b, y, u) & FORBIDDEN == 0) == (
                y == life(n, b) and u == witness[n, b])
            neighborhoods += 1

    # Exhaust every pair, including all wrong output/helper assignments.
    assignments = list(product(range(9), range(2), range(2), range(2)))
    two_cells = 0
    for a, b in product(assignments, repeat=2):
        ns, bs, ys, us = zip(a, b)
        vals = dict(S=pack([n+c for n, c in zip(ns, bs)]), B=pack(bs),
                    Y=pack(ys), U=pack(us), J=1+RADIX)
        v = run(LOCAL, vals)['V']
        vd = [digit(*a), digit(*b)]
        assert v == pack(vd)
        assert (v & (FORBIDDEN*vals['J']) == 0) == all(
            y == life(n, c) and u == witness[n, c]
            for n, c, y, u in (a, b))
        two_cells += 1

    # Exact small tests of the arbitrary-mask popcount lemma, including P+M>=L.
    carry_tests = carry_overflow = 0
    for bits in range(1, 8):
        L = 1 << bits
        for p, m in product(range(L), repeat=2):
            r = (L-p)*(L-1)+m
            upper = bits+m.bit_count()
            assert r.bit_count() <= upper
            assert (r.bit_count() == upper) == (p & m == 0)
            if p+m >= L:
                assert r.bit_count() < upper
                carry_overflow += 1
            carry_tests += 1

    rng = random.Random(20260922)
    wrapped = correct = corrupt = 0
    for length in (1, 2, 3, 7, 16, 31):
        q = WRAPPER_RADIX**length
        J = (q-1)//511
        for case in range(20):
            ns = [rng.randrange(9) for _ in range(length)]
            bs = [rng.randrange(2) for _ in range(length)]
            ys = [life(n, b) for n, b in zip(ns, bs)]
            us = [witness[n, b] for n, b in zip(ns, bs)]
            if case % 2:
                pos = rng.randrange(length)
                ys[pos] ^= 1
            inputs = dict(q=q, J=J, S=pack([n+b for n, b in zip(ns, bs)],512),
                          B=pack(bs,512), Y=pack(ys,512), U=pack(us,512))
            env = run(WRAPPER, inputs)
            Vprime = pack([2*digit(n, b, y, u)+1
                           for n, b, y, u in zip(ns, bs, ys, us)],512)
            assert env['Vprime'] == Vprime
            assert env['ones_left'] == env['ones_right']
            assert env['P'] == Vprime+q*(inputs['B']+q*inputs['U'])
            assert env['M'] == J*(144+510*(q+q*q))
            assert 0 < env['P'] < q**3 < env['Lambda'] == q**4
            assert 0 < env['M'] < q**3
            assert env['M'].bit_count() == 18*length
            assert env['P'] % 2 == 1 and env['M'] % 2 == 0
            assert env['r'] % 2 == 1
            assert q**3 <= env['r'] < q**8 < 2*(q**3)**3
            assert env['D0'] == (q**3)**2 == 2**(54*length)
            mask_ok = env['P'] & env['M'] == 0
            semantic_ok = all(y == life(n, b) and u == witness[n, b]
                              for n, b, y, u in zip(ns, bs, ys, us))
            assert mask_ok == semantic_ok == (case % 2 == 0)
            assert env['r'].bit_count() <= 54*length
            assert (env['r'].bit_count() == 54*length) == mask_ok
            correct += int(mask_ok)
            corrupt += int(not mask_ok)
            wrapped += 1

    # Mask extraction is checked independently of already Boolean input words.
    extraction = 0
    # Independently exhaust each radix512 block, then the Boolean/mixed product.
    mixed_mask = 144+510*(512+512**2)
    for slot, x in product(range(3),range(512)):
        expected = (x & 144 == 0) if slot == 0 else x in (0,1)
        assert (x*512**slot & mixed_mask == 0) == expected
        extraction += 1
    for b, u, v in product(range(2), range(2), range(512)):
        P = v+512*b+512**2*u
        M = 144+510*(512+512**2)
        assert (P & M == 0) == (v & 144 == 0)
        extraction += 1

    # Two discovery/derivation variants, not part of the selected source count.
    variants = [
        ('neighbor_sum_radix256', 256, 68,
         lambda n,b,y,u: 103+7*n-b+63*y+27*u, (102,249)),
        ('inclusive_sum_radix512', 512, 136,
         lambda n,b,y,u: 17*(n+b)-b+84+120*u+8*y, (84,364)),
    ]
    variant_tests = 0
    for _, radix, mask, expression, bounds in variants:
        digits = []
        for n,b,y in product(range(9),range(2),range(2)):
            vals = [expression(n,b,y,u) for u in range(2)]
            assert any(v & mask == 0 for v in vals) == (y == life(n,b))
            assert all(0 <= v < radix for v in vals)
            digits.extend(vals)
            variant_tests += len(vals)
        assert (min(digits), max(digits)) == bounds

    return dict(
        status='LIFE_ONE_FIELD_MASK_PASS', universality_status='NOT_CLAIMED',
        review='Author and two independent complete scoped proof/source reviews and fresh receipt checks PASS; a further independent calculation checks the selected scalar relation and26-operation schedule.',
        radix=RADIX, forbidden_mask=FORBIDDEN,
        expression='V=14S+B+8Y+59U+20J; S=N+B',
        local_operations=8, local_histogram=histogram(LOCAL),
        shifted_local_operations=9, shifted_local_histogram=histogram(SHIFTED_LOCAL),
        shifted_expression='Vprime=28S+2B+16Y+118U+41J=2V+J',
        wrapper_radix=512, shifted_forbidden_mask=144, shifted_digit_bounds=[41,429],
        conditional_wrapper_operations=26, conditional_wrapper_histogram=histogram(WRAPPER),
        extra_Boolean_planes=1, digit_bounds=[20,214],
        local_schedule=LOCAL, shifted_local_schedule=SHIFTED_LOCAL, wrapper_schedule=WRAPPER,
        ones_equality=['ones_left','ones_right'],
        scalar_assignments=scalar, scalar_table=table,
        full_neighborhood_assignments=neighborhoods,
        exhaustive_two_cell_assignments=two_cells,
        arbitrary_mask_popcount_checks=carry_tests,
        arbitrary_mask_overflow_checks=carry_overflow,
        wrapped_cases=wrapped, wrapped_correct=correct, wrapped_corrupted=corrupt,
        exhaustive_one_cell_field_extractions=extraction,
        alternate_scalar_assignments=variant_tests,
        symbolic_source_identities=len(formulas),
        scope='Local truth table plus a conditional mask/index wrapper. The radix power, neighbor and time alignment, Boolean output, pre-kernel untyped bounds, zero-plane positive adapters, universality and input/target interfaces are not supplied by the count.',
        proof_note='../1980/EXPLORATION_LIFE_ONE_FIELD_MASK.md')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'], 'local8=4M4A; conditional26=14M12A')
