#!/usr/bin/env python3
"""Exact conditional base-three Pell component; no universal bound claimed."""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
from round37_1980_base_two_pell_regression import pell_power

PARAMETERS = ['q', 'P0']
CORE_NAMES = ['a', 'c', 'd', 'f', 'h', 'i', 'j', 'k', 'o', 'r', 's',
              'w', 'tau', 'eta', 'zeta', 'ga', 'y_aux']
SYM = {name: sp.Symbol(name) for name in PARAMETERS + CORE_NAMES}
OUTER = [
    ('q2', '*', 'q', 'q'), ('L', '*', 'q2', 'q2'),
    ('n2', '*', 9, 'L'), ('pP', '*', 3, 'P0'),
    ('gap', '-', 'n2', 'pP'), ('r_rhs', '-', 'gap', 1),
]
CORE = [
    ('wn2', '*', 'w', 'n2'), ('sn2', '*', 's', 'n2'),
    ('UM', '*', 'wn2', 'sn2'), ('R12', '+', 'UM', 'sn2'),
    ('ksn2', '*', 'k', 'sn2'), ('UM2', '*', 'UM', 'UM'),
    ('scaled_norm_coefficient', '+', 'UM2', 'wn2'),
    ('ratio_product2', '*', 'ksn2', 'ksn2'),
    ('L9', '*', 'scaled_norm_coefficient', 'ratio_product2'),
    ('tauplus1', '+', 'tau', 1), ('R9', '*', 'tau', 'tauplus1'),
    ('R10a', '+', 'ksn2', 'eta'), ('R10b', '+', 'eta', 'zeta'),
    ('r1', '+', 'r', 1), ('hpm1', '*', 'h', 'UM'),
    ('R11', '+', 'r1', 'hpm1'), ('tr1', '+', 'r1', 'r'),
    ('cam2', '*', 'c', 'a'), ('D1', '+', 'wn2', 'cam2'),
    ('six_a', '*', 6, 'a'), ('modulus', '+', 'six_a', 8),
    ('gam', '*', 'ga', 'modulus'), ('R14', '+', 'D1', 'gam'),
    ('a_square', '*', 'a', 'a'), ('discriminant', '+', 'a_square', 'modulus'),
    ('c2', '*', 'c', 'c'), ('Ac2', '*', 'discriminant', 'c2'),
    ('R15', '+', 'Ac2', 1), ('L15', '*', 'd', 'd'),
    ('ic2', '*', 'i', 'c2'), ('ic22', '*', 'ic2', 'ic2'),
    ('L16', '*', 'f', 'f'), ('f_square_minus_one', '-', 'L16', 1),
    ('R16', '*', 'discriminant', 'f_square_minus_one'),
    ('of', '*', 'o', 'f'), ('aux_u_rhs', '+', 'c', 'of'),
    ('jc', '*', 'j', 'c'), ('H17', '+', 'tr1', 'jc'),
    ('H2', '*', 'H17', 'H17'), ('aux_y2', '*', 'y_aux', 'y_aux'),
    ('aux_square_gap', '-', 'H2', 'aux_y2'),
    ('L17', '*', 'ic22', 'aux_square_gap'), ('P17', '-', 1, 'aux_y2'),
]
SCHEDULE = OUTER + CORE
EQUALITIES = [
    ('r', 'r_rhs'), ('L9', 'R9'), ('c', 'R10a'), ('k', 'R10b'),
    ('k', 'R11'), ('a', 'R12'), ('d', 'R14'), ('L15', 'R15'),
    ('ic22', 'R16'), ('L17', 'P17'), ('H17', 'aux_u_rhs'),
]


def source_residuals():
    z = SYM
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y = [z[n] for n in CORE_NAMES]
    scale = 9*z['q']**4
    U,Y = w*scale,s*scale
    Q = U*Y**2
    D = a*a+6*a+8
    aux_u = 2*r+1+j*c
    return [
        r-scale+3*z['P0']+1,
        Q*(Q+1)*k*k-tau*(tau+1),
        c-Y*k-eta, k-eta-zeta, k-r-1-h*U*Y,
        a-Y*(U+1), d-U-a*c-ga*(6*a+8),
        d*d-D*c*c-1, (i*c*c)**2-D*(f*f-1),
        D*(f*f-1)*(aux_u*aux_u-y*y)-(1-y*y),
        aux_u-c-o*f,
    ]


def verify_certificate():
    need = baseline.need
    need(len(OUTER) == 6 and len(CORE) == 43, 'six outer and43 core operations')
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    aux_u = 2*SYM['r']+1+SYM['j']*SYM['c']
    correction = source[8]*(aux_u**2-SYM['y_aux']**2)
    records = []
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left]-env[right])
        adjustment = correction if index == 9 else sp.Integer(0)
        need(sp.expand(actual-residual-adjustment) == 0,
             'fresh source residual '+str(index))
        records.append(dict(index=index, equality=[left,right],
                            source=sp.sstr(sp.expand(residual)),
                            actual=sp.sstr(actual),
                            correction=sp.sstr(sp.expand(adjustment))))
    need(len(records) == len(source) == len(EQUALITIES) == 11, 'all eleven equations')
    primitives, counts = verify_primitives(SCHEDULE, env)
    need(len(primitives) == 49 and counts == {'+':20,'*':29}, 'exact49 conditional operations')
    core_hist = {op: sum(row[1] == op for row in CORE) for op in ('*','+','-')}
    need(core_hist['*'] == 25 and core_hist['+']+core_hist['-'] == 18,
         'core is25 multiplications and18 additions/subtractions')
    need(len(CORE_NAMES) == 17, 'seventeen supplied positive Pell witnesses')
    need(all(s.free_symbols <= set(SYM.values()) for s in source), 'source symbols declared')
    used = {operand for row in SCHEDULE for operand in row[2:]}
    used |= {operand for pair in EQUALITIES for operand in pair}
    need(set(SYM) <= used, 'every supplied input is used')
    need(sp.expand(env['discriminant']-(SYM['a']+3)**2+1) == 0,
         'main discriminant is exactly(a+3)^2-1')
    need(sp.expand(env['modulus']-(6*SYM['a']+8)) == 0, 'base-three modulus')
    return dict(
        status='ARITHMETIC_PASS_CONDITIONAL_BASE_THREE_COMPONENT',
        arithmetic_status='PASS', universality_status='NOT_CLAIMED',
        operations=49, outer_operations=6, retained_pell_operations=43,
        histogram=histogram, primitive_histogram=counts, core_histogram=core_hist,
        parameters=PARAMETERS, positive_unknowns=CORE_NAMES, unknown_count=17,
        input_domains={'q':'integer >=2','P0':'integer,0<=P0<q^4',
                      'core_witnesses':'positive integers','intermediate_registers':'integers'},
        converse_extra_hypotheses='q is a power of three; P0 is ternary Boolean and even',
        source_bound_cost_included=False, parity_enforcement_cost_included=False,
        equations=11, primitive_instructions=primitives, equalities=EQUALITIES,
        residuals=records, proof='../1980/EXPLORATION_BASE_THREE_PELL_KERNEL.md',
        scope='Conditional power-of-three and central-binomial divisibility component; excludes packed-word construction/bound, parity enforcement, local computation, raw input and halting interfaces. No universal operation bound.')


def check_recurrence():
    total = 0
    for A in range(3, 18):
        for b in range(2, A):
            modulus = 2*A*b-b*b-1
            for j in range(18):
                chi, psi = pell_power(A, j)
                assert (chi+(b-A)*psi-pow(b,j,modulus)) % modulus == 0
                total += 1
    return total


def check_canonical_ratio(r):
    J = 2*r+1
    U = 3**J
    numerator, denominator = (U+1)**(2*r), U**r
    Y, tail = divmod(numerator, denominator)
    a = Y*(U+1)
    A, D = a+3, (a+3)**2-1
    E, Q = U*Y, U*Y*Y
    P = 2*Q+1
    d,c = pell_power(A,J)
    first_chi,k = pell_power(P,r+1)
    assert d*d-D*c*c == 1
    assert first_chi*first_chi-(P*P-1)*k*k == 1
    error = c*denominator-k*numerator
    error_denominator = k*denominator
    assert error > 0
    assert error*(U+1) < 24*r*error_denominator
    assert 2*error < error_denominator
    assert 6*tail < denominator
    eta = c-Y*k
    zeta = k-eta
    assert eta > 0 and zeta > 0
    assert 10*Q > a and 12*r < a
    assert (2*P-1)-4*A == 4*Y*(U*(Y-1)-1)-11 > 0
    assert Y >= U**r and a > U**(r+1) > 3**J
    h,h_rem = divmod(k-r-1,E)
    tau,tau_rem = divmod(first_chi-1,2)
    gamma,ga_rem = divmod(d-U-a*c,6*a+8)
    assert h > 0 and tau > 0 and gamma > 0
    assert h_rem == tau_rem == ga_rem == 0
    assert tau*(tau+1) == (E*E+U)*(Y*k)**2
    return dict(r=r,J=J,U_bits=U.bit_length(),A_bits=A.bit_length(),
                c_bits=c.bit_length(),k_bits=k.bit_length(),
                exact_both_norms=True,positive_integral_tau_h_gamma=True,
                lower_ratio_and_upper_error=True,exact_rounding=True,
                fractional_tail_below_one_sixth=True,positive_interval=True,
                exponent_decoding_growth=True)


def check_mask_hypotheses():
    """Actual admissible mask inputs, without constructing huge Pell witnesses."""
    def factorial_valuation(n):
        result = 0
        while n:
            n //= 3
            result += n
        return result

    rows = []
    for q in (3,9,27):
        for packed in (0,4,10,40):
            L,scale = q**4,9*q**4
            n0,r = 3*q*q,scale-3*packed-1
            digits = []
            rest = packed
            while rest:
                rest,digit = divmod(rest,3)
                digits.append(digit)
            assert all(digit <= 1 for digit in digits)
            assert 0 <= packed < L and packed % 2 == r % 2 == 0
            assert 6*L < r < scale == n0*n0 and n0 < r
            assert scale*scale > r+1 and scale*(scale+1) > 2*r+1
            valuation = factorial_valuation(2*r)-2*factorial_valuation(r)
            exponent,rest = 0,scale
            while rest > 1:
                assert rest % 3 == 0
                exponent,rest = exponent+1,rest//3
            assert valuation == exponent
            rows.append(dict(q=q,P0=packed,r=r,D0=scale,
                             central_binomial_valuation=valuation,
                             exact_preliminary_hypotheses=True,
                             even_ternary_boolean_input=True))
    return rows


def verify():
    result = verify_certificate()
    result['regression'] = dict(
        recurrence_cases=check_recurrence(),
        admissible_mask_hypothesis_cases=check_mask_hypotheses(),
        canonical_ratio_cases=[check_canonical_ratio(r) for r in (2,3,4,8,16,32,64,98)],
        arithmetic='Exact integer powers and cross-multiplied rational inequalities',
        auxiliary_witnesses_materialized=False,
        scope='Canonical Pell-coordinate checks, not full packed-word component witnesses; the general proof establishes the unbounded positive converse')
    return result


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(result['arithmetic_status'],result['operations'],result['primitive_histogram'])
    print(result['retained_pell_operations'],'Pell operations;',result['equations'],'equalities')
    print(result['regression']['recurrence_cases'],'recurrence cases;',
          len(result['regression']['canonical_ratio_cases']),'canonical ratio cases')
    print('Conditional component only; no universal operation bound claimed.')
