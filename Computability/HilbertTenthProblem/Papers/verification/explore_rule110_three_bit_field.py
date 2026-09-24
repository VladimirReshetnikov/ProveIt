#!/usr/bin/env python3
"""Exact local Rule 110 components; no complete universal count is claimed."""
from __future__ import annotations

from collections import Counter
from itertools import product
import json
from pathlib import Path


BINARY_SET = {0, 1, 2, 3, 8, 9, 10, 11}
TERNARY_SET = {0, 1, 3, 4, 9, 10, 12, 13}
BINARY_SCHEDULE = [
    ('T', '+', 'B', 'C'), ('T3', '*', 3, 'T'),
    ('Y4', '*', 4, 'Y'), ('V', '+', 'A', 'T3'),
    ('VY', '+', 'V', 'Y4'), ('U', '+', 'J', 'VY'),
]
ABSORBED_BINARY_SCHEDULE = [
    ('C307', '*', 307, 'C'), ('Y4', '*', 4, 'Y'),
    ('V', '+', 'C307', 'Y4'), ('U', '+', 'J', 'V'),
]
TERNARY_SCHEDULE = [
    ('T', '+', 'B', 'C'), ('T4', '*', 4, 'T'),
    ('Y2', '*', 2, 'Y'), ('J3', '*', 3, 'J'),
    ('V', '+', 'A', 'T4'), ('VY', '+', 'V', 'Y2'),
    ('Z', '+', 'J3', 'VY'),
]
ABSORBED_TERNARY_SCHEDULE = [
    ('C841', '*', 841, 'C'), ('Y2', '*', 2, 'Y'),
    ('J3', '*', 3, 'J'), ('V', '+', 'C841', 'Y2'),
    ('Z', '+', 'J3', 'V'),
]
PACKING_SCHEDULE = [
    ('qW', '*', 'q', 'W'), ('YqW', '+', 'Y', 'qW'),
    ('qYqW', '*', 'q', 'YqW'), ('P', '+', 'U', 'qYqW'),
]
MASK_SCHEDULE = [
    ('qp1', '+', 'q', 1), ('qqp1', '*', 'q', 'qp1'),
    ('M14', '*', 14, 'qqp1'), ('Mfactor', '+', 'M14', 4),
    ('M', '*', 'J', 'Mfactor'),
]
MASK_WITH_SQUARE_SCHEDULE = [
    ('q2pq', '+', 'q2', 'q'), ('M14', '*', 14, 'q2pq'),
    ('Mfactor', '+', 'M14', 4), ('M', '*', 'J', 'Mfactor'),
]
IMPLICIT_MASK_SCHEDULE = [
    ('M15', '*', 15, 'M'), ('q10', '*', 10, 'q'),
    ('M15q10', '+', 'M15', 'q10'), ('left', '+', 'M15q10', 4),
    ('right', '*', 14, 'n'),
]


def rule(a, b, c):
    return (110 >> (4*a + 2*b + c)) & 1


def pack(digits, radix):
    return sum(d * radix**i for i, d in enumerate(digits))


def in_digit_set(word, radix, allowed, n):
    if not 0 <= word < radix**n:
        return False
    for _ in range(n):
        if word % radix not in allowed:
            return False
        word //= radix
    return True


def execute(schedule, values):
    env = dict(values)
    for name, operation, left, right in schedule:
        assert name not in env
        a = env[left] if isinstance(left, str) else left
        b = env[right] if isinstance(right, str) else right
        env[name] = a+b if operation == '+' else a*b
    return env


def count(schedule):
    counts = Counter(op for _, op, _, _ in schedule)
    return dict(operations=len(schedule), multiplications=counts['*'], additions=counts['+'])


def affine_search(allowed):
    found = []
    branches = 0
    for e, s1, s2, s3, s4 in product(sorted(allowed), repeat=5):
        branches += 1
        a, b, c, y = s4-e, s3-s1, s3-s2, s1+s2-s3-e
        if not a or not y:
            continue
        if any(v not in allowed for v in
               (s4+s1-e, s4+s2-e, s4+2*s3-s1-s2)):
            continue
        coefficients = (e, a, b, c, y)
        if any(e+a*av+b*bv+c*cv+y*(1-rule(av, bv, cv)) in allowed
               for av, bv, cv in product(range(2), repeat=3)):
            continue
        for av, bv, cv, yv in product(range(2), repeat=4):
            assert ((e+a*av+b*bv+c*cv+y*yv in allowed)
                    == (yv == rule(av, bv, cv)))
        found.append(coefficients)
    assert branches == 32768
    return found


def verify_local():
    rows = []
    for a, b, c in product(range(2), repeat=3):
        y = rule(a, b, c)
        u = 1+a+3*(b+c)+4*y
        z = 3+a+4*(b+c)+2*y
        wrong_u = 1+a+3*(b+c)+4*(1-y)
        wrong_z = 3+a+4*(b+c)+2*(1-y)
        assert u in BINARY_SET and wrong_u not in BINARY_SET
        assert z in TERNARY_SET and wrong_z not in TERNARY_SET
        rows.append(dict(a=a, b=b, c=c, y=y, u=u, z=z,
                         wrong_u=wrong_u, wrong_z=wrong_z))
    packed_checks = Counter()
    for cells in product(list(product(range(2), repeat=4)), repeat=3):
        expected = all(y == rule(a, b, c) for a, b, c, y in cells)
        for radix, allowed, schedule, out in (
                (16, BINARY_SET, BINARY_SCHEDULE, 'U'),
                (27, TERNARY_SET, TERNARY_SCHEDULE, 'Z')):
            fields = {name: pack([cell[i] for cell in cells], radix)
                      for i, name in enumerate(('A', 'B', 'C', 'Y'))}
            fields['J'] = (radix**3-1)//(radix-1)
            env = execute(schedule, fields)
            assert in_digit_set(env[out], radix, allowed, 3) == expected
            packed_checks[radix] += 1
    absorbed_checks = Counter()
    for n in range(3, 9):
        for bits in product(range(2), repeat=n-2):
            for radix, schedule, absorbed, out in (
                    (16, BINARY_SCHEDULE, ABSORBED_BINARY_SCHEDULE, 'U'),
                    (27, TERNARY_SCHEDULE, ABSORBED_TERNARY_SCHEDULE, 'Z')):
                C = pack(bits, radix)
                B, A = radix*C, radix**2*C
                J = (radix**n-1)//(radix-1)
                ys = [rule((A//radix**i) % radix,
                           (B//radix**i) % radix,
                           (C//radix**i) % radix) for i in range(n)]
                Y = pack(ys, radix)
                env = dict(A=A, B=B, C=C, Y=Y, J=J)
                assert execute(schedule, env)[out] == execute(absorbed, env)[out]
                absorbed_checks[radix] += 1
    return dict(truth_table=rows, packed_cases=dict(packed_checks),
                absorbed_cases=dict(absorbed_checks))


def mask_parameters(n):
    q = 16**n
    J = (q-1)//15
    L = q**3
    M = J*(4+14*q+14*q*q)
    assert M.bit_count() == 7*n
    values = dict(q=q, q2=q*q, J=J, M=M, n=L)
    assert execute(MASK_SCHEDULE, {k: v for k, v in values.items() if k != 'M'})['M'] == M
    assert execute(MASK_WITH_SQUARE_SCHEDULE,
                   {k: v for k, v in values.items() if k != 'M'})['M'] == M
    implicit = execute(IMPLICIT_MASK_SCHEDULE, values)
    assert implicit['left'] == implicit['right']
    return q, J, L, M


def verify_mask():
    checks = Counter()
    q, J, L, M = mask_parameters(1)
    for U, Y, W in product(range(q), repeat=3):
        P = U+q*Y+q*q*W
        assert execute(PACKING_SCHEDULE, dict(q=q, U=U, Y=Y, W=W))['P'] == P
        expected = U in BINARY_SET and Y in (0, 1) and W in (0, 1)
        assert ((P & M) == 0) == expected
        r = (L-P)*(L-1)+M
        assert (r.bit_count() >= 19) == expected
        checks['complete_one_cell_words'] += 1
        checks['complete_one_cell_accepted'] += int(expected)
        checks['complete_one_cell_overflows'] += int(P+M >= L)
    for n in (2, 3):
        q, J, L, M = mask_parameters(n)
        uwords = [pack(ds, 16) for ds in product(sorted(BINARY_SET), repeat=n)]
        bitwords = [pack(ds, 16) for ds in product(range(2), repeat=n)]
        forbidden_bits = [1 << i for i in range(12*n) if M & (1 << i)]
        for U, Y, W in product(uwords, bitwords, bitwords):
            P = U+q*Y+q*q*W
            assert P < L and not P & M
            r = (L-P)*(L-1)+M
            assert r.bit_count() == 19*n
            checks['multi_cell_valid_words'] += 1
            for bit in forbidden_bits:
                bad = P | bit
                rb = (L-bad)*(L-1)+M
                assert bad & M and rb.bit_count() < 19*n
                checks['forbidden_bit_corruptions'] += 1
    return dict(checks)


def main():
    binary = affine_search(BINARY_SET)
    ternary = affine_search(TERNARY_SET)
    assert len(binary) == 66 and (1, 1, 3, 3, 4) in binary
    assert len(ternary) == 18 and (3, 1, 4, 4, 2) in ternary
    schedules = dict(binary_aligned=count(BINARY_SCHEDULE),
                     binary_absorbed=count(ABSORBED_BINARY_SCHEDULE),
                     ternary_aligned=count(TERNARY_SCHEDULE),
                     ternary_absorbed=count(ABSORBED_TERNARY_SCHEDULE),
                     packing=count(PACKING_SCHEDULE),
                     mask=count(MASK_SCHEDULE),
                     mask_with_square_available=count(MASK_WITH_SQUARE_SCHEDULE),
                     implicit_mask_with_cube_available=count(IMPLICIT_MASK_SCHEDULE))
    assert schedules['binary_aligned'] == dict(operations=6, multiplications=2, additions=4)
    assert schedules['binary_absorbed'] == dict(operations=4, multiplications=2, additions=2)
    assert schedules['ternary_aligned'] == dict(operations=7, multiplications=3, additions=4)
    assert schedules['ternary_absorbed'] == dict(operations=5, multiplications=3, additions=2)
    result = dict(
        status='RULE110_THREE_BIT_FIELD_LOCAL_PASS',
        schedules=schedules,
        affine_search=dict(branches_per_fixed_set=32768,
                           binary_set_projections=len(binary),
                           ternary_set_projections=len(ternary),
                           binary_candidates=binary, ternary_candidates=ternary),
        local=verify_local(), mixed_mask=verify_mask(),
        proof_note='../1980/EXPLORATION_RULE110_THREE_BIT_FIELD.md',
        review_status=dict(author='PASS', independent='Two complete proof/source/dependency reviews and fresh verification PASS, with no findings.'),
        complete_system_operation_count=None, universality_status='OPEN',
        scope=('Conditional local relation only. Boolean input/output planes, repunit, '
               'alignment, bounds, mask realization, kernel and complete computation '
               'interface are separate obligations. No total reduction is asserted.'))
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print(json.dumps(dict(schedules=schedules, local={k: v for k, v in result['local'].items()
                                                    if k != 'truth_table'},
                          mixed_mask=result['mixed_mask']), indent=2))


if __name__ == '__main__':
    main()
