#!/usr/bin/env python3
"""Exact arithmetic for a fixed-radix finite-history research system.

This defines a decidable finite-history relation for the two row
parameters I,F. It is not a universal certificate. See the complete
characterization and component proof notes.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round37_1980_binary_product_certificate as published
from round13_1980_certificate import verify_primitives


PARAMETERS = ['I', 'F']
CORE_NAMES = ['a','c','d','f','h','i','j','k','o','r','s','w',
              'tau','eta','zeta','ga','y_aux']
OUTER_NAMES = ['q','v','quot','hrow','Bw','Cw','Yw','Dw','Xw','Ew','Zw',
               'alpha','alphaI','lam']
NAMES = PARAMETERS + OUTER_NAMES + CORE_NAMES
SYM = {name: sp.Symbol(name) for name in NAMES}

OUTER = [
    ('Q','*','q','q'),
    ('Q2','*','Q','Q'),
    ('Q4','*','Q2','Q2'),
    ('Lbig','*','Q4','Q4'),
    ('n2','*','Lbig','Q4'),
    ('vq','*','v','quot'),
    ('W','*','v','v'),
    ('Qm1','-','Q',1),
    ('Wm1','-','W',1),
    ('row_geom','*','hrow','Wm1'),
    ('Aw','*',4,'Bw'),
    ('fourC','*',4,'Cw'),
    ('XD','+','Xw','Dw'),
    ('BC','+','Bw','Cw'),
    ('XDD','+','XD','Dw'),
    ('AD','+','Aw','Dw'),
    ('twoE','*',2,'Ew'),
    ('ZE2','+','Zw','twoE'),
    ('YE','+','Yw','Ew'),
    ('ABC','+','Aw','BC'),
    ('bound','+','ABC','alpha'),
    ('Ibound','+','I','alphaI'),
    ('WY','*','W','Yw'),
    ('time_lhs','+','I','WY'),
    ('QF','*','Q','F'),
    ('time_rhs','+','Bw','QF'),
    ('Bh','+','Bw','hrow'),
    ('pack0','*','Q','Bh'),
    ('pack1','+','Zw','pack0'),
    ('pack2','*','Q','pack1'),
    ('pack3','+','Ew','pack2'),
    ('pack4','*','Q','pack3'),
    ('pack5','+','Xw','pack4'),
    ('pack6','*','Q','pack5'),
    ('pack7','+','Dw','pack6'),
    ('pack8','*','Q','pack7'),
    ('packed','+','Bw','pack8'),
    ('three_lam','*',3,'lam'),
    ('mask_scale','+','three_lam',1),
    ('packing_gap','-','Lbig','packed'),
    ('r_product','*','packing_gap','three_lam'),
    ('two_lam','*',2,'lam'),
    ('r_lhs','+','r_product','two_lam'),
]
CORE = [row for row in published.SCHEDULE[33:77] if row[0] != 'R13']
SCHEDULE = OUTER + CORE
OUTER_EQUALITIES = [
    ('q','vq'), ('Qm1','row_geom'), ('Bw','fourC'),
    ('BC','XDD'), ('AD','ZE2'), ('YE','XD'),
    ('bound','Q'), ('Ibound','W'), ('time_lhs','time_rhs'),
    ('mask_scale','Lbig'), ('r','r_lhs'),
]
CORE_EQUALITIES = [
    ('L9','R9'), ('c','R10a'), ('k','R10b'), ('k','R11'),
    ('a','R12'), ('d','R14'), ('L15','R15'), ('ic22','R16'),
    ('L17','P17'), ('H17','aux_u_rhs'),
]
EQUALITIES = OUTER_EQUALITIES + CORE_EQUALITIES


def source_residuals():
    z = SYM
    q,v,quot,hrow,B,C,Yw,Dw,Xw,Ew,Zw,alpha,alphaI,lam = [z[k] for k in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y = [z[k] for k in CORE_NAMES]
    Q,W,Lbig,scale = q*q,v*v,q**16,q**24
    Aw = 4*B
    packed = B+Q*(Dw+Q*(Xw+Q*(Ew+Q*(Zw+Q*(B+hrow)))))
    U,Yp = w*scale,s*scale
    Dpell = a*a+4*a+3
    K,aux_u = Dpell*(f*f-1),2*r+1+j*c
    return [
        q-v*quot,
        Q-1-hrow*(W-1),
        B-4*C,
        B+C-Xw-2*Dw,
        Aw+Dw-Zw-2*Ew,
        Yw+Ew-Xw-Dw,
        Aw+B+C+alpha-Q,
        z['I']+alphaI-W,
        z['I']+W*Yw-B-Q*z['F'],
        3*lam+1-Lbig,
        r-(Lbig-packed)*3*lam-2*lam,
        U*Yp*Yp*(U*Yp*Yp+1)*k*k-tau*(tau+1),
        c-Yp*k-eta,
        k-eta-zeta,
        k-r-1-h*U*Yp,
        a-Yp*(U+1),
        d-U-a*c-ga*(4*a+3),
        d*d-Dpell*c*c-1,
        (i*c*c)**2-Dpell*(f*f-1),
        K*(aux_u*aux_u-y*y)-(1-y*y),
        aux_u-c-o*f,
    ]


def verify_certificate():
    baseline.need(len(OUTER) == len(CORE) == 43, '43 outer and 43 retained kernel instructions')
    baseline.need(all('n' not in row and 'ka' not in row for row in CORE),
                  'retained kernel uses only the squared scale and no second index')
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    z = SYM
    aux_u = 2*z['r']+1+z['j']*z['c']
    correction = source[18]*(aux_u*aux_u-z['y_aux']**2)
    records = []
    for index, ((left,right), residual) in enumerate(zip(EQUALITIES,source)):
        actual = sp.expand(env[left]-env[right])
        adjustment = correction if index == 19 else sp.Integer(0)
        if sp.expand(actual-residual-adjustment) == 0:
            sign = 1
        elif adjustment == 0 and sp.expand(actual+residual) == 0:
            sign = -1
        else:
            raise AssertionError('fresh residual mismatch at '+str(index))
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(residual)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(adjustment))))
    baseline.need(len(records) == len(source) == len(EQUALITIES) == 21,
                  '21 fresh source equations')
    baseline.need(records[18]['correction'] == '0', 'auxiliary norm prerequisite is exact')
    primitives, counts = verify_primitives(SCHEDULE,env)
    baseline.need(len(primitives) == 86, 'exact integrated arithmetic count')
    baseline.need(set(NAMES) <= {operand for row in SCHEDULE for operand in row[2:]} |
                  {operand for pair in EQUALITIES for operand in pair},
                  'every supplied input participates')
    baseline.need(sp.expand(env['n2']-SYM['q']**24) == 0,
                  'only squared Pell scale is materialized')
    return dict(status='ARITHMETIC_PASS_FOR_NONUNIVERSAL_HISTORY_COMPONENTS',
                arithmetic_status='PASS',universality_status='DECIDABLE_ROW_PARAMETER_RELATION',
                operations=86,histogram=histogram,primitive_histogram=counts,
                outer_operations=43,retained_pell_operations=43,
                parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=len(OUTER_NAMES+CORE_NAMES),equations=len(EQUALITIES),
                primitive_instructions=primitives,equalities=EQUALITIES,residuals=records,
                missing='A fixed universal computation model with fully paid raw-input, boundary and halt interfaces. For these fixed row parameters, the running time is bounded by valuation_4(I), so the relation is decidable.',
                characterization='../1980/EXPLORATION_RULE110_FIXED_INPUT_BOUND.md',
                proof_notes=['../1980/EXPLORATION_ALIGNED_BOOLEAN_TABLEAUX.md',
                             '../1980/EXPLORATION_PERIODIC_DIGIT_MASK.md',
                             '../1980/BASE_TWO_PELL_90_PROOF.md'],
                scope='Exact combined arithmetic for a decidable finite Rule 110 history relation. No universal bound below 90 is claimed.')


if __name__ == '__main__':
    receipt = verify_certificate()
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(receipt['arithmetic_status'],receipt['operations'],receipt['primitive_histogram'])
    print('Decidable row-parameter relation; no universal bound below 90.')
