#!/usr/bin/env python3
"""Exact power-of-two Boolean-mask identities and radix-16 scale interface."""
import json
from collections import Counter
from math import comb, isqrt
from pathlib import Path

import sympy as sp


def v2(value):
    assert value > 0
    return (value & -value).bit_length() - 1


def boolean_digits(value, radix):
    while value:
        value, digit = divmod(value, radix)
        if digit > 1:
            return False
    return True


def verify_schedule():
    q, P, lam = sp.symbols('q P lambda')
    env = {'q': q, 'P': P, 'lambda': lam}
    schedule = [
        ('q2', '*', 'q', 'q'),
        ('q4', '*', 'q2', 'q2'),
        ('q6', '*', 'q4', 'q2'),
        ('L', '*', 'q4', 'q4'),
        ('D0', '*', 'L', 'q6'),
        ('fifteen_lambda', '*', 15, 'lambda'),
        ('L_check', '+', 'fifteen_lambda', 1),
        ('gap', '-', 'L', 'P'),
        ('product', '*', 'gap', 'fifteen_lambda'),
        ('M', '*', 14, 'lambda'),
        ('r', '+', 'product', 'M'),
    ]
    counts = Counter()
    for name, op, left, right in schedule:
        a = env[left] if isinstance(left, str) else sp.Integer(left)
        b = env[right] if isinstance(right, str) else sp.Integer(right)
        assert name not in env
        env[name] = {'*': lambda: a*b, '+': lambda: a+b,
                     '-': lambda: a-b}[op]()
        counts['+' if op == '-' else op] += 1
    assert len(schedule) == 11
    assert counts == {'*': 8, '+': 3}
    assert env['L'] == q**8 and env['D0'] == q**14
    assert env['D0'] == (q**7)**2
    expected = (q**8-P)*(q**8-1)+14*lam
    residual = env['L_check']-env['L']
    assert sp.expand(env['r']-expected-(q**8-P)*residual) == 0
    return {'total': 11, 'multiplications': 8, 'additions_subtractions': 3,
            'power_multiplications': 5,
            'inputs': ['q', 'P', 'lambda'],
            'free_equality': 'L_check = L',
            'squared_scale': 'D0 = q^14 = (q^7)^2',
            'explicit_N0_register': False,
            'symbolic_source_identity': 'PASS',
            'instructions': [list(row) for row in schedule]}


def verify_extended_interfaces():
    q, P, lam = sp.symbols('q P lambda')
    configurations = [
        (64, 0, 6, 11,
         [('q2','q','q'),('q3','q2','q'),('q5','q3','q2'),
          ('L','q3','q3'),('D0','L','q5')]),
        (64, 0, 12, 22,
         [('q2','q','q'),('q4','q2','q2'),('q6','q4','q2'),
          ('q10','q6','q4'),('L','q6','q6'),('D0','L','q10')]),
        (128, 1, 7, 13,
         [('q2','q','q'),('q3','q2','q'),('q6','q3','q3'),
          ('L','q6','q'),('D0','L','q6')])]
    records = []
    for radix, bit, length_exp, scale_exp, products in configurations:
        env = {'q': q, 'P': P, 'lambda': lam}
        for name, left, right in products:
            assert name not in env
            env[name] = env[left]*env[right]
        assert env['L'] == q**length_exp
        assert env['D0'] == q**scale_exp
        coefficient = radix-1-(1 << bit)
        r_poly = (env['L']-P)*((radix-1)*lam)+coefficient*lam
        residual = (radix-1)*lam+1-env['L']
        expected = (env['L']-P)*(env['L']-1)+coefficient*lam
        assert sp.expand(r_poly-expected-(env['L']-P)*residual) == 0
        bound_rows = []
        # Non-powers of two are retained whenever the mask geometry is integral.
        for qv in (4,5,8,11,13,16,17,19,32,64,128,129,131):
            Lv = qv**length_exp
            if (Lv-1) % (radix-1):
                continue
            Dv = qv**scale_exp
            nv = qv**(length_exp-1 if length_exp <= 7 else scale_exp//2)
            lv = (Lv-1)//(radix-1)
            for Pv in (0, 1, Lv//2, Lv-1):
                rv = (Lv-Pv)*(radix-1)*lv+coefficient*lv
                assert nv >= 64 and nv < rv < 2*nv**3
                assert Dv >= nv*nv
                assert Dv*Dv > 2*rv+1
                assert 8*rv < Dv*Dv
                assert Dv < rv*rv
            bound_rows.append({'q':qv, 'power_of_two':qv & (qv-1) == 0,
                               'scale_square_before_decoding':
                                   scale_exp % 2 == 0 or isqrt(qv)**2 == qv})
        k = radix.bit_length()-1
        alignment_cases = 0
        for e in range(2,65):
            assert length_exp*e % k == 0
            digit_count = length_exp*e//k
            assert scale_exp*e == (2*k-1)*digit_count
            qv = 1 << e
            for m in range(1,e+1):
                W = 1 << (k*m)
                divides = (qv-1) % (W-1) == 0
                assert divides == (e % (k*m) == 0)
                if divides:
                    t = e//(k*m)
                    H = (qv-1)//(W-1)
                    assert qv == W**t == radix**(m*t)
                    assert H == sum(W**j for j in range(t))
                    assert boolean_digits(H,radix)
                    alignment_cases += 1
        records.append({'radix':radix,'selected_bit':bit,
                        'length_exponent':length_exp,'scale_exponent':scale_exp,
                        'power_products':[list(row) for row in products],
                        'operations':len(products)+6,
                        'multiplications':len(products)+3,
                        'additions_subtractions':3,
                        'pre_power_bound_samples':bound_rows,
                        'admissible_field_alignment_cases':alignment_cases,
                        'threshold_exponent_identity':'PASS'})
    selected_cases = 0
    selected_overflows = 0
    for k in range(2,8):
        R = 1 << k
        for bit in range(k):
            for N in (1,2):
                L = R**N
                M = (R-1-(1 << bit))*(L-1)//(R-1)
                assert M.bit_count() == (k-1)*N
                for P in range(L):
                    r = (L-P)*(L-1)+M
                    carry = P.bit_count()+M.bit_count()-(P+M).bit_count()
                    overflow = P+M >= L
                    assert r.bit_count() == (2*k-1)*N-carry-(v2(P) if overflow else 0)
                    accepted = P & M == 0
                    assert (r.bit_count() >= (2*k-1)*N) == accepted
                    assert r % 2 == (M-P) % 2
                    if accepted:
                        assert P % (1 << bit) == 0
                        assert boolean_digits(P >> bit,R)
                        if bit:
                            assert P % 2 == 0 and r % 2 == 1
                    selected_cases += 1
                    selected_overflows += overflow
    # Verify the precise retained arithmetic interface, rather than infer it
    # from the proof-only name N0 in earlier notes.
    import round37_1980_binary_product_certificate as published
    kernel = [row for row in published.SCHEDULE[33:77] if row[0] != 'R13']
    inputs = {operand for row in kernel for operand in row[2:]
              if isinstance(operand,str)} - {row[0] for row in kernel}
    assert len(kernel) == 43 and 'n2' in inputs and 'n' not in inputs
    assert [row[0] for row in kernel if 'n2' in row[2:]] == ['wn2','sn2']
    return {'interfaces':records,'selected_bit_predicate_cases':selected_cases,
            'selected_bit_overflow_cases':selected_overflows,
            'retained_kernel_operations':43,
            'scale_used_only_in':['U=w*D0','Y=s*D0'],
            'odd_index_positive_witness_reference':'../1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md'}


def verify():
    rows = []
    direct_binomial_cases = 0
    for k, max_N in ((2, 8), (3, 5), (4, 4), (5, 3)):
        R = 1 << k
        cases = overflows = boolean_cases = 0
        for N in range(1, max_N+1):
            L = R**N
            M = (R-2)*(L-1)//(R-1)
            threshold = (2*k-1)*N
            assert M.bit_count() == (k-1)*N
            for P in range(L):
                r = (L-P)*(L-1)+M
                carries = P.bit_count()+M.bit_count()-(P+M).bit_count()
                assert carries >= 0
                overflow = P+M >= L
                correction = v2(P) if overflow else 0
                if overflow:
                    assert carries >= 1
                    overflows += 1
                assert r.bit_count() == threshold-carries-correction
                boolean = boolean_digits(P, R)
                assert boolean == (P & M == 0)
                assert boolean == (carries == 0)
                assert (r.bit_count() >= threshold) == boolean
                assert r.bit_count() <= threshold
                assert (r & 1) == (P & 1)
                assert 0 < r < L*L
                if N == 1 or (k == 2 and N == 2):
                    central = comb(2*r, r)
                    assert v2(central) == r.bit_count()
                    assert (central % (1 << threshold) == 0) == boolean
                    direct_binomial_cases += 1
                cases += 1
                boolean_cases += boolean
        rows.append({'radix': R, 'k': k, 'N_range': [1, max_N],
                     'all_P_cases': cases, 'addition_overflows': overflows,
                     'Boolean_cases': boolean_cases})
    bounds = []
    for q in (4, 7, 8, 11, 13, 16, 17, 31, 32):
        L, D0, N0 = q**8, q**14, q**7
        assert (L-1) % 15 == 0
        lam = (L-1)//15
        samples = sorted(set((0, 1, L//2, L-2, L-1)))
        for P in samples:
            r = (L-P)*(15*lam)+14*lam
            assert N0 >= 64
            assert N0 < L-1 < r < q**16 < N0**3
            assert D0 == N0*N0
            assert D0*D0 > r+1
            assert D0*D0 > 2*r+1
            assert 8*r < D0*D0
        bounds.append({'q': q, 'power_of_two': q & (q-1) == 0,
                       'P_values': [str(p) for p in samples],
                       'pre_power_bounds': 'PASS'})
    alignments = 0
    for e in range(2, 65):
        q = 1 << e
        assert q**8 == 16**(2*e)
        assert q**14 == 1 << (7*2*e)
        for m in range(1, e+1):
            v, W = 1 << m, 1 << (4*m)
            assert q % v == 0
            divides = (q-1) % (W-1) == 0
            assert divides == (e % (4*m) == 0)
            if divides:
                t = e//(4*m)
                H = (q-1)//(W-1)
                assert q == W**t == 16**(m*t)
                assert H == sum(W**j for j in range(t))
                assert boolean_digits(H, 16)
                alignments += 1
    return {
        'status': 'PASS',
        'scope': ('Exact finite corroboration of a general popcount theorem, '
                  'the radix-16 pre-Pell scale interface, and an 11-operation '
                  'local schedule; not a full Life or universal certificate.'),
        'proof': '../1980/EXPLORATION_GENERAL_RADIX_BOOLEAN_MASK.md',
        'general_radix_cases': rows,
        'total_predicate_cases': sum(row['all_P_cases'] for row in rows),
        'total_addition_overflows': sum(row['addition_overflows'] for row in rows),
        'direct_central_binomial_cases': direct_binomial_cases,
        'pre_power_bound_cases': bounds,
        'power_of_two_threshold_cases': 63,
        'admissible_field_alignment_cases': alignments,
        'schedule': verify_schedule(),
        'extended_interfaces': verify_extended_interfaces(),
        'necessity_parity_scope': 'Retained positive auxiliary construction requires even P.'}


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'], result['total_predicate_cases'], 'predicate cases;',
          result['total_addition_overflows'], 'overflows;',
          result['schedule']['total'], 'outer operations;',
          result['extended_interfaces']['selected_bit_predicate_cases'],
          'selected-bit cases', flush=True)
