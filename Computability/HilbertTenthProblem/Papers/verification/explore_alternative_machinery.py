#!/usr/bin/env python3
"""Exact checks for conditional building blocks, not a universality certificate.

These checks concern proposed alternatives to the Jones coefficient compiler.
No aggregate operation bound or complete arithmetic history verifier is claimed.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
import json
from pathlib import Path

import round37_1980_binary_product_certificate as published


def pack(bits, radix=4):
    return sum(bit * radix**i for i, bit in enumerate(bits))


def rule110(a, b, c):
    return (110 >> (4*a + 2*b + c)) & 1


def local_relations(a, b, c, y, d, x, e, z):
    return b+c == x+2*d and a+d == z+2*e and y+e == x+d


RULE_SCHEDULE = [
    ('T', '+', 'X', 'D'), ('BC', '+', 'B', 'C'),
    ('TD', '+', 'T', 'D'), ('AD', '+', 'A', 'D'),
    ('E2', '*', 2, 'E'), ('ZE2', '+', 'Z', 'E2'),
    ('YE', '+', 'Y', 'E'),
]


def local_schedule(values):
    env = dict(zip(('A', 'B', 'C', 'Y', 'D', 'X', 'E', 'Z'), values))
    for name, operation, left, right in RULE_SCHEDULE:
        lhs = env[left] if isinstance(left, str) else left
        rhs = env[right] if isinstance(right, str) else right
        env[name] = lhs+rhs if operation == '+' else lhs*rhs
    return env['BC'] == env['TD'] and env['AD'] == env['ZE2'] and env['YE'] == env['T']


def verify_rule110():
    valid = []
    checked = 0
    for a, b, c, y in product(range(2), repeat=4):
        witnesses = []
        for d, x, e, z in product(range(2), repeat=4):
            checked += 1
            assert local_schedule((a, b, c, y, d, x, e, z)) == local_relations(a, b, c, y, d, x, e, z)
            if local_relations(a, b, c, y, d, x, e, z):
                witnesses.append((d, x, e, z))
        assert len(witnesses) == int(y == rule110(a, b, c))
        if witnesses:
            valid.append(dict(a=a, b=b, c=c, y=y, auxiliary=witnesses[0]))
    packed_checks = 0
    for cells in product(list(product(range(2), repeat=3)), repeat=3):
        planes = [[] for _ in range(8)]
        for a, b, c in cells:
            d, x = b*c, b ^ c
            e, z = a*d, a ^ d
            values = (a, b, c, rule110(a, b, c), d, x, e, z)
            for plane, value in zip(planes, values):
                plane.append(value)
        packed_values = tuple(pack(plane) for plane in planes)
        assert local_relations(*packed_values) and local_schedule(packed_values)
        packed_checks += 1
    counts = Counter(row[1] for row in RULE_SCHEDULE)
    assert counts == {'+': 6, '*': 1}
    return dict(status='PASS', local_assignments=checked,
                accepted_local_assignments=valid, packed_three_cell_cases=packed_checks,
                operations=len(RULE_SCHEDULE), multiplications=counts['*'], additions=counts['+'],
                schedule=RULE_SCHEDULE,
                hypotheses='All eight finite planes have base-R digits 0 or 1; R>=4.',
                omitted_costs='Digit restrictions, common tableau alignment, boundaries, input and halt.')


def verify_geometry():
    checked = 0
    for total in range(1, 33):
        assert (2**(2*total)-1) > 0  # The equation rules out v=1, W=1.
        for width in range(1, total+1):
            q, v = 2**total, 2**width
            Q, W = q*q, v*v
            assert q == v*(q//v)
            assert ((Q-1) % (W-1) == 0) == (total % width == 0)
            if total % width == 0:
                height = total//width
                h = (Q-1)//(W-1)
                assert h == sum(W**j for j in range(height))
                assert (W-1)*h == Q-1
            checked += 1
    return dict(status='PASS', cases=checked,
                equations=['q=v*d', 'Q=q*q', 'W=v*v', 'Q-1=h*(W-1)'],
                hypotheses='q>1 is a power of two; all variables are positive integers. The last equation excludes v=1.',
                conclusion='Q=4^N, W=4^m, m divides N, and h is the row-start mask.',
                scope='Geometry only; no boundary, input, halt or transition predicate.')


def verify_tag_step():
    checked = 0
    for deletion in range(1, 5):
        K = 2**deletion
        for append_length in range(1, 5):
            for appendant in product(range(2), repeat=append_length):
                U, M = pack(appendant, 2), 2**append_length
                for length in range(deletion, deletion+4):
                    for word in product(range(2), repeat=length):
                        N, Z = pack(word, 2), 2**length
                        s, d = word[0], N % K
                        tail = word[deletion:]
                        next_word = tail + (appendant if s else (0,))
                        next_N, next_Z = pack(next_word, 2), 2**len(next_word)
                        shared = s*Z
                        assert K*next_N == N-d+U*shared
                        assert K*next_Z == 2*Z+(M-2)*shared
                        assert d == s+2*(d//2) and 0 <= d < K
                        assert 0 <= next_N < next_Z
                        checked += 1
    return dict(status='PASS', exact_word_steps=checked,
                rules=['0 -> 0', '1 -> fixed appendant u'],
                identities=['K*N_next=N-d+U*(s*Z)',
                            'K*Z_next=2*Z+(M-2)*(s*Z)', 'd=s+2*h'],
                hypotheses='K=2^deletion, M=2^len(u), U is little-endian u, Z=2^len(word), len(word)>=deletion.',
                scope='One-step identities only; tested small rules are not claimed universal.')


def verify_retained_pell_count():
    rows = published.SCHEDULE[33:77]
    assert len(rows) == 44 and rows[0][0] == 'wn2' and rows[-1][0] == 'P17'
    assert [row for row in rows if row[0] == 'R13'] == [('R13', '+', 'ka', 'phi')]
    retained = [row for row in rows if row[0] != 'R13']
    counts = Counter(row[1] for row in retained)
    assert len(retained) == 43
    forbidden = {'ka', 'mu', 'phi', 'rho', 'Delta', 'Tindex', 'th'}
    assert not any(isinstance(v, str) and v in forbidden for row in retained for v in row)
    return dict(status='PASS', retained_operations=43, histogram=dict(counts),
                deleted_operations=14,
                deleted_one_based_instructions=[51, *range(78, 91)],
                precomputed='n2=n*n is supplied by the outer arithmetic schedule.',
                proof_reference='../1980/BASE_TWO_PELL_90_PROOF.md, sections 1-5 for soundness and applicable first-Pell parts of section 6 for positive witnesses; second index and exponent omitted.',
                hypotheses='Soundness requires n>=64 and n<=r<2*n^3 before decoding. Positive necessity also requires power-of-two n, even r, and n^2 dividing the central binomial coefficient.',
                scope='Counted reusable subsystem; not a 43-operation universal system.')


if __name__ == '__main__':
    result = dict(status='CONDITIONAL_COMPONENTS_PASS', universality_status='OPEN',
                  rule110=verify_rule110(), geometry=verify_geometry(),
                  binary_tag_step=verify_tag_step(), retained_pell=verify_retained_pell_count(),
                  complete_system_operation_count=None,
                  scope='Exact component checks and inherited subsystem count only. Published universal bound remains 90.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'], '; universality OPEN; complete operation count unavailable')
    print('Rule110 local cases:', result['rule110']['local_assignments'])
    print('Tag exact steps:', result['binary_tag_step']['exact_word_steps'])
    print('Geometry cases:', result['geometry']['cases'])
    print('Retained Pell operations:', result['retained_pell']['retained_operations'])
