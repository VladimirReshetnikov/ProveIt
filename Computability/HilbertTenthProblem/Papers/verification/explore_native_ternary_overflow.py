#!/usr/bin/env python3
"""Sharp native-mask window and exact60 four-field relation; no universal claim."""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_base_three_positive_kernel as native

PARAMETERS = ['q','F0','F1','F2','F3']
AUXILIARIES = ['rep','alpha']+native.CORE_NAMES
SYM = {name:sp.Symbol(name) for name in PARAMETERS+AUXILIARIES}
PREFIX = [
    ('twice_rep','+','rep','rep'), ('q_rhs','+','twice_rep',1),
    ('pair_left','+','F0','F3'), ('pair_right','+','F1','F2'),
    ('bound_rhs','+','q','rep'), ('bound','+','pair_left','alpha'),
    ('pack0','*','q','F3'), ('pack1','+','F2','pack0'),
    ('pack2','*','q','pack1'), ('pack3','+','F1','pack2'),
    ('pack4','*','q','pack3'), ('packed','+','F0','pack4'),
]
OUTER = [tuple('packed' if value == 'P0' else value for value in row)
         for row in native.OUTER]
SCHEDULE = PREFIX+OUTER+native.CORE
EQUALITIES = [('q','q_rhs'),('pair_left','pair_right'),('bound','bound_rhs')]+native.EQUALITIES


def source_residuals():
    z = SYM
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y = [z[n] for n in native.CORE_NAMES]
    q = z['q']
    packed = z['F0']+q*z['F1']+q*q*z['F2']+q**3*z['F3']
    scale = 3*q**4
    U,Y = w*scale,s*scale
    Q,D = U*Y**2,a*a+6*a+8
    aux_u = 2*r+1+j*c
    return [
        q-2*z['rep']-1,
        z['F0']+z['F3']-z['F1']-z['F2'],
        z['F0']+z['F3']+z['alpha']-q-z['rep'],
        r-3*packed-2,
        Q*(Q+1)*k*k-tau*(tau+1),
        c-Y*k-eta, k-eta-zeta, k-r-1-h*U*Y,
        a-Y*(U+1), d-U-a*c-ga*(6*a+8),
        d*d-D*c*c-1, (i*c*c)**2-D*(f*f-1),
        D*(f*f-1)*(aux_u*aux_u-y*y)-(1-y*y),
        aux_u-c-o*f,
    ]


def verify_certificate():
    need = baseline.need
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE,env)
    source = source_residuals()
    aux_u = 2*SYM['r']+1+SYM['j']*SYM['c']
    correction = source[11]*(aux_u**2-SYM['y_aux']**2)
    records = []
    for index,((left,right),residual) in enumerate(zip(EQUALITIES,source)):
        actual = sp.expand(env[left]-env[right])
        adjustment = correction if index == 12 else sp.Integer(0)
        need(sp.expand(actual-residual-adjustment) == 0,'fresh source '+str(index))
        records.append(dict(index=index,equality=[left,right],
                            source=sp.sstr(sp.expand(residual)),actual=sp.sstr(actual),
                            correction=sp.sstr(sp.expand(adjustment))))
    need(len(records) == len(source) == len(EQUALITIES) == 14,'all14 equations')
    primitives,counts = verify_primitives(SCHEDULE,env)
    need(len(PREFIX) == 12 and len(OUTER) == 5 and len(native.CORE) == 43,
         '12 packing/bound,5 mask,43 Pell operations')
    need(len(primitives) == 60 and counts == {'+':28,'*':32},'exact60 primitives')
    need(len(AUXILIARIES) == 19 and len(PARAMETERS) == 5,'complete positive input domains')
    need(all(p.free_symbols <= set(SYM.values()) for p in source),'all source symbols declared')
    used = {operand for row in SCHEDULE for operand in row[2:]}
    used |= {operand for pair in EQUALITIES for operand in pair}
    need(set(SYM) <= used,'every supplied input used')
    return dict(
        status='PASS_COMPLETE_BOUNDED_FOUR_NATIVE_FIELD_RELATION',
        arithmetic_status='PASS',universality_status='NOT_CLAIMED',
        operations=60,primitive_histogram=counts,histogram=histogram,
        packing_and_bound_operations=12,mask_operations=5,pell_operations=43,
        parameters=PARAMETERS,positive_auxiliaries=AUXILIARIES,auxiliary_count=19,
        input_domains='All five input integers and nineteen supplied auxiliaries are positive; arithmetic registers are integers.',
        unpaid_numeric_guards=False,unpaid_packed_word_bound=False,
        unpaid_parity_test=False,equations=14,primitive_instructions=primitives,
        equalities=EQUALITIES,residuals=records,
        proof='../1980/EXPLORATION_NATIVE_TERNARY_OVERFLOW.md',
        scope='Exactly the bounded four-native-field equal-pair relation with shared positive slack. No counter seed, universal control, raw input or halting construction is included.')


def valuation_factorial(n):
    answer = 0
    while n:
        n //= 3
        answer += n
    return answer


def central_valuation(r):
    return valuation_factorial(2*r)-2*valuation_factorial(r)


def carry_count(r):
    answer,carry = 0,0
    while r or carry:
        r,digit = divmod(r,3)
        carry = (2*digit+carry)//3
        answer += carry
    return answer


def is_native(word,length):
    for _ in range(length):
        word,digit = divmod(word,3)
        if digit not in (1,2):
            return False
    return word == 0


def check_extended_masks():
    cases,overflow = 0,0
    endpoints,domains = [],[]
    for N in range(1,11):
        L = 3**N
        star = (3*L-1)//2
        for packed in range(star):
            r = 3*packed+2
            valuation = central_valuation(r)
            assert valuation == carry_count(r)
            expected = packed < L and is_native(packed,N)
            assert (valuation >= N+1) == expected
            if packed >= L:
                assert valuation <= N
                overflow += 1
            cases += 1
        assert central_valuation(3*(star-1)+2) <= N
        assert central_valuation(3*star+2) == N+2
        assert central_valuation(3*(star+1)+2) == N+2
        endpoints.append(dict(N=N,L=L,last_rejected=star-1,
                              first_false_acceptance=star,
                              second_false_acceptance=star+1,
                              exact_false_valuation=N+2))
        domains.append(dict(N=N,all_words_checked=star))
    return dict(complete_cases=cases,rejected_overflow_cases=overflow,
                domains=domains,sharp_endpoints=endpoints)


def check_preliminary_bounds():
    rows = []
    for q in range(3,61):
        L,scale = q**4,3*q**4
        # Largest integer strictly below3(L-1)/2, valid also at even q.
        last = (3*(L-1)-1)//2
        for packed in sorted({q**3,L-1,L,last}):
            assert q**3 <= packed and 2*packed < 3*(L-1)
            r = 3*packed+2
            assert scale >= 243 and r >= 83
            assert 2*r < 3*scale-5 and scale < r*r
            assert scale*scale > r+1 and scale*(scale+1) > 2*r+1
            assert 12*r < scale*(scale+1)
            rows.append(dict(q=q,P0=packed,D0=scale,r=r))
        # Broader kernel lemma includes the full r<2D0 endpoint.
        r = 2*scale-1
        assert scale*scale > r+1 and scale*(scale+1) > 2*r+1
        assert 12*r < scale*(scale+1)
    return rows


def check_fields():
    cases = accepted = overflow = 0
    first_overflow = None
    boundary_cases = 0
    for e in range(1,4):
        q = 3**e
        H,L = (q-1)//2,q**4
        for pair in range(2,3*H+1):
            alpha = q+H-pair
            assert alpha > 0
            for F0 in range(1,pair):
                F3 = pair-F0
                for F1 in range(1,pair):
                    F2 = pair-F1
                    fields = (F0,F1,F2,F3)
                    packed = sum(value*q**i for i,value in enumerate(fields))
                    assert q**3 < packed and 2*packed < 3*(L-1)
                    assert max(fields) < 3*H
                    assert packed % 2 == 0
                    r = 3*packed+2
                    actual = central_valuation(r) >= 4*e+1
                    expected = all(is_native(value,e) for value in fields)
                    assert actual == expected
                    if actual:
                        assert packed < L and max(fields) < q
                        assert is_native(packed,4*e)
                    if packed >= L:
                        overflow += 1
                        assert not actual
                        if first_overflow is None:
                            first_overflow = dict(q=q,fields=fields,alpha=alpha,
                                                  packed=packed,L=L,r=r)
                    if pair == 3*H:
                        boundary_cases += 1
                    cases += 1
                    accepted += actual
    assert first_overflow is not None and boundary_cases > 0
    return dict(all_pair_and_slack_tuples=cases,accepted_tuples=accepted,
                rejected_packed_overflows=overflow,first_overflow=first_overflow,
                allowed_R_equals_3H_cases=boundary_cases)


def check_even_counterfamily():
    rows = []
    for e in range(1,7):
        q = 3**e
        N,L = 4*e,q**4
        packed = (3*L+1)//2
        scale,r = 3*L,3*packed+2
        assert packed >= L and packed % 2 == r % 2 == 0
        assert is_native(packed,N+1)
        assert central_valuation(r) == N+2
        assert r >= 83 and r < 2*scale and scale < r*r
        rows.append(dict(q=q,P0=packed,D0=scale,r=r,valuation=N+2,
                         positive_Pell_extension='Exists by enlarged even-r kernel converse; not numerically materialized'))
    return rows


def check_padding():
    cases = 0
    for e in range(1,5):
        q = 3**e
        H = (q-1)//2
        words = [n for n in range(q) if is_native(n,e)]
        by_sum = {}
        for F0 in words:
            for F3 in words:
                by_sum.setdefault(F0+F3,[]).append((F0,F3))
        for pair,pairs in by_sum.items():
            for F0,F3 in pairs:
                for F1,F2 in pairs:
                    new_q,new_H = 3*q,H+q
                    fields = tuple(value+q for value in (F0,F1,F2,F3))
                    assert all(is_native(value,e+1) for value in fields)
                    new_pair = pair+2*q
                    assert new_pair == fields[0]+fields[3] == fields[1]+fields[2]
                    assert new_pair < 3*new_H
                    assert new_q+new_H-new_pair > 0
                    cases += 1
    return cases


def verify():
    result = verify_certificate()
    result['regression'] = dict(
        extended_masks=check_extended_masks(),
        preliminary_bounds=check_preliminary_bounds(),
        complete_field_tuples=check_fields(),
        even_endpoint_counterfamily=check_even_counterfamily(),
        one_column_padding_cases=check_padding(),
        unchanged_large_Pell_coordinate_regressions_rerun=False,
        scope='Exact new carry windows, bounds, field decoding and source identities. Existing exact Pell-coordinate checks remain in the frozen base-three notes; the new general proof checks every enlarged hypothesis. No huge auxiliary tuple is materialized.')
    return result


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(result['arithmetic_status'],result['operations'],result['primitive_histogram'],result['equations'])
    checks = result['regression']
    print(checks['extended_masks']['complete_cases'],'complete mask cases;',
          checks['complete_field_tuples']['all_pair_and_slack_tuples'],'field tuples')
    print('Complete bounded four-field relation; no universal construction claimed.')
