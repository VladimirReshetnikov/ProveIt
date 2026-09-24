#!/usr/bin/env python3
"""Refuted 89-operation candidate: bound the packed S and use n=q^5.

All arithmetic checks are exact. The intended representation is refuted
by a full false-code family with Tplus>n. Fixed numerals are free.
This does not replace the published round37 result.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round37_1980_binary_product_certificate as previous
from round13_1980_certificate import verify_primitives

OUT = Path(__file__).with_suffix('.json')
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name:sp.Symbol(name) for name in NAMES}
EQUALITIES = [('L1','n') if pair == ('L1','q') else
              ('n','q5') if pair == ('n','q8') else pair
              for pair in previous.EQUALITIES]
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUATION_LABELS[0] = 'packed S positive bound'
EQUATION_LABELS[5] = 'fifth power packing scale'


def make_schedule():
    expected = {
        'q8':('q8','*','q4','q4'),
        'bound_sum':('bound_sum','+','l','sigma'),
        'L1':('L1','+','bound_sum','al'),
        'S':('S','+','g','Sq4'),
    }
    result = []
    seen = set()
    for row in previous.SCHEDULE:
        name = row[0]
        if name in expected:
            baseline.need(row == expected[name], 'exact predecessor instruction '+name)
            seen.add(name)
        if name in ('bound_sum','L1'):
            continue
        result.append(('q5','*','q4','q') if name == 'q8' else row)
        if name == 'S':
            result.append(('L1','+','S','al'))
    baseline.need(seen == set(expected), 'all and only intended predecessor edits located')
    return result


SCHEDULE = make_schedule()


def source_residuals():
    s = SYM
    x,a,b,c,d,e,f,g,h,i,j,k,ell,n,o,q,r,ss,t,w = (
        s[name] for name in ('x','a','b','c','d','e','f','g','h','i','j',
                            'k','l','n','o','q','r','s','t','w'))
    B,A,C = s['H']+b+2,a+2,x+g
    D,U,Y = A*A-1,w*n*n,ss*n*n
    la,th = s['la'],s['th']
    product = (e-ell)*C*C
    S = g+q*q*(ell+e*q+q*q*product)
    Tplus = q*q*(1+th*la)+ell*(th*q**4-b)
    K,aux_u = D*(f*f-1),2*r+1+j*c
    aux_y2 = s['y_aux']**2
    return [
        S+s['al']-n,
        b-x-s['beta'],
        q*q-1-la*(B-1),
        th+2-B,
        ell+e*q-s['V']-t*th,
        n-q**5,
        r-S*(n*n-n)-Tplus*(n*n-1),
        U*Y*Y*(U*Y*Y+1)*k*k-s['tau']*(s['tau']+1),
        c-Y*k-s['eta'],
        k-s['eta']-s['zeta'],
        k-r-1-h*U*Y,
        a-Y*(U+1),
        c-s['ka']-s['phi'],
        d-U-a*c-s['ga']*(4*a+3),
        d*d-D*c*c-1,
        (i*c*c)**2-D*(f*f-1),
        K*(aux_u*aux_u-aux_y2)-(1-aux_y2),
        s['mu']-q-s['ka']*(A-B)-s['rho']*(D-(A-B)**2),
        D*s['ka']**2+1-s['mu']**2,
        s['ka']-s['Tindex']-s['Delta']*a,
        product-s['sigma'],
        aux_u-c-o*f,
    ]


def verify_certificate():
    env,old_env = dict(SYM),dict(previous.SYM)
    histogram = baseline.run_schedule(SCHEDULE,env)
    baseline.run_schedule(previous.SCHEDULE,old_env)
    changed = sorted(name for name in env.keys() & old_env.keys()
                     if sp.expand(env[name]-old_env[name]) != 0)
    baseline.need(changed == ['L1'], 'only the common bound register changes')
    baseline.need('q8' not in env and 'bound_sum' not in env and 'q5' in env,
                  'obsolete registers removed and fifth power constructed')
    source,s = source_residuals(),SYM
    A,B = s['a']+2,s['H']+s['b']+2
    u = 2*s['r']+1+s['j']*s['c']
    corrections = {
        2:-s['la']*source[3],
        16:source[15]*(u*u-s['y_aux']**2),
        17:source[3]*(s['ka']+s['rho']*(source[3]-2*(A-B))),
    }
    baseline.need(len(source) == len(EQUALITIES) == 22,
                  '22 fresh source residuals and equality tests')
    records = []
    for index,((left,right),residual) in enumerate(zip(EQUALITIES,source)):
        actual = sp.expand(env[left]-env[right])
        correction = corrections.get(index,sp.Integer(0))
        if sp.expand(actual-residual-correction) == 0:
            sign = 1
        elif correction == 0 and sp.expand(actual+residual) == 0:
            sign = -1
        else:
            raise AssertionError('residual mismatch at '+EQUATION_LABELS[index])
        records.append(dict(equation=EQUATION_LABELS[index],equality=[left,right],
            source_residual_polynomial=sp.sstr(sp.expand(residual)),
            certificate_residual_polynomial=sp.sstr(actual),source_residual_sign=sign,
            triangular_correction_polynomial=sp.sstr(sp.expand(correction))))
    for index in (3,15):
        baseline.need(records[index]['triangular_correction_polynomial'] == '0',
                      'triangular correction prerequisites are independently exact')
    old_source = previous.source_residuals()
    deltas = {0:env['S']-s['l']-s['sigma']+s['q']-s['n'],
              5:s['q']**8-s['q']**5}
    for index,(old,new) in enumerate(zip(old_source,source)):
        baseline.need(sp.expand(new-old-deltas.get(index,0)) == 0,
                      'fresh source matches exactly the two declared changes')
    primitives,counts = verify_primitives(SCHEDULE,env)
    baseline.need(len(primitives) == 89 and counts == {'+':41,'*':48},
                  '89 arithmetic operations with fixed numerals free')
    used = {operand for _,_,left,right in SCHEDULE for operand in (left,right)
            if isinstance(operand,str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, 'every positive supplied input participates')
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4,
                  '34 positive unknowns and four supplied inputs')
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  'every source symbol is declared')
    numerals = sorted({operand for row in primitives for operand in (row['left'],row['right'])
                       if isinstance(operand,int)})
    baseline.need(numerals == [1,3,4], 'all literal numerals remain free')
    return dict(status='ARITHMETIC_PASS_BUT_REPRESENTATION_REFUTED',arithmetic_status='PASS',
        universality_status='REFUTED_FOR_CURRENT_COMPILER',
        counterexample='../1980/EXPLORATION_PACKED_BOUND_Q5_COUNTEREXAMPLE.md',
        failure='Asymmetric code aliases preserve the fixed index and central-binomial condition with Tplus>n; an inconsistent-circuit index admits x=1 with every supplied unknown positive.',
        operations=89,straight_line_histogram=histogram,
        additions_and_multiplications_only=dict(additions=41,multiplications=48),
        unknowns=34,equations=22,equality_tests=22,parameters=PARAMETERS,
        positive_input_names=NAMES,
        positive_unknown_names=[name for name in NAMES if name not in PARAMETERS],
        primitive_instructions=primitives,equalities=EQUALITIES,residual_polynomials=records,
        changed_registers=changed,removed_registers=['q8','bound_sum'],new_registers=['q5'],
        changed_source_indices_zero_based=[0,5],
        source_change_polynomials={str(i):sp.sstr(sp.expand(v)) for i,v in deltas.items()},
        literal_numerals=numerals,
        proof_note='../1980/PACKED_BOUND_89_CANDIDATE.md',
        scope='Exact arithmetic certificate, preliminary Pell recovery and canonical necessity for a candidate whose intended representation is refuted; not an 89-operation universality theorem.')


if __name__ == '__main__':
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(receipt['status'],'arithmetic',receipt['arithmetic_status'],receipt['operations'],receipt['straight_line_histogram'])
    print(receipt['unknowns'],'positive unknowns;',receipt['equations'],'equalities; intended representation REFUTED')
