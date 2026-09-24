#!/usr/bin/env python3
"""Exact 81-operation finite history certificate using its length directly."""
from pathlib import Path
import json
import sympy as sp

import round42_1980_implicit_history_bound as previous
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

PARAMETERS = previous.PARAMETERS
OUTER_NAMES, CORE_NAMES = previous.OUTER_NAMES, previous.CORE_NAMES
NAMES, SYM = previous.NAMES, previous.SYM
OUTER = [(name,op,'q' if left == 'Q' else left,'q' if right == 'Q' else right)
         for name,op,left,right in previous.OUTER if name != 'Q']
CORE = previous.CORE
SCHEDULE = OUTER+CORE
EQUALITIES = previous.EQUALITIES


def source_residuals():
    z = SYM
    q,v,quot,H,B,C,Yw,Dw,Xw,Ew,Zw,alphaI,lam = [z[name] for name in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y = [z[name] for name in CORE_NAMES]
    W,L,scale = v*v,q**8,q**12
    P = Dw+q*Xw+q*q*Ew+q**3*Zw+q**7*(B+H)
    U,Yp = w*scale,s*scale
    Dpell = a*a+4*a+3
    K,aux_u = Dpell*(f*f-1),2*r+1+j*c
    return [
        q-v*quot,
        q-1-H*(W-1),
        B-4*C,
        B+C-Xw-2*Dw,
        4*B+Dw-Zw-2*Ew,
        Yw+Ew-Xw-Dw,
        z['I']+alphaI-v,
        z['I']+W*Yw-C-q*z['F'],
        3*lam+1-L,
        r-(L-P)*3*lam-2*lam,
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
    need = baseline.need
    need(len(OUTER) == 38 and len(CORE) == 43, '38 outer and 43 Pell instructions')
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE,env)
    source = source_residuals()
    z = SYM
    aux_u = 2*z['r']+1+z['j']*z['c']
    correction = source[17]*(aux_u**2-z['y_aux']**2)
    records = []
    for index, ((left,right),residual) in enumerate(zip(EQUALITIES,source)):
        actual = sp.expand(env[left]-env[right])
        adjustment = correction if index == 18 else sp.Integer(0)
        if sp.expand(actual-residual-adjustment) == 0:
            sign = 1
        elif adjustment == 0 and sp.expand(actual+residual) == 0:
            sign = -1
        else:
            raise AssertionError('fresh residual mismatch at '+str(index))
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(residual)),actual=sp.sstr(actual),
                            correction=sp.sstr(sp.expand(adjustment))))
    need(len(records) == len(source) == len(EQUALITIES) == 20, '20 fresh source equations')
    need(records[17]['correction'] == '0', 'exact auxiliary norm prerequisite')
    primitives,counts = verify_primitives(SCHEDULE,env)
    need(len(primitives) == 81 and counts == {'+':37,'*':44}, 'exact 81 operations')
    need(len(OUTER_NAMES+CORE_NAMES) == 30, 'same 30 positive unknowns')
    need(set(NAMES) <= {operand for row in SCHEDULE for operand in row[2:]} |
         {operand for pair in EQUALITIES for operand in pair}, 'all supplied inputs used')
    need(all(residual.free_symbols <= set(SYM.values()) for residual in source),
         'all source variables declared')
    need('Q' not in env and all('Q' not in row for row in SCHEDULE),
         'total length is supplied q, not a square register')
    need(sp.expand(env['n2']-z['q']**12) == 0, 'squared scale uses four products')
    expected = z['Dw']+z['q']*z['Xw']+z['q']**2*z['Ew']+z['q']**3*z['Zw']+z['q']**7*(z['Bw']+z['hrow'])
    need(sp.expand(env['packed']-expected) == 0, 'direct-length sparse packing')

    # Independently verify the forward positive witness reparameterization.
    old_source = previous.source_residuals()
    substitution = {z['q']:z['q']**2,z['quot']:z['q']*z['quot']}
    for index,(new,old) in enumerate(zip(source,old_source)):
        expected = z['q']*old if index == 0 else old
        need(sp.expand(new.subs(substitution,simultaneous=True)-expected) == 0,
             'forward witness map source '+str(index))
    return dict(status='ARITHMETIC_PASS_FOR_DIRECT_LENGTH_HISTORY',
                arithmetic_status='PASS',universality_status='NOT_ESTABLISHED',
                operations=81,histogram=histogram,primitive_histogram=counts,
                parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=30,equations=20,outer_operations=38,
                retained_pell_operations=43,
                length='Q=q; geometry derives q=(v^2)^t after the first exponential',
                squared_pell_scale='q^12',
                forward_witness_map={'q_new':'q_old^2','quot_new':'q_old*quot_old'},
                forward_source_map_verified=True,
                primitive_instructions=primitives,equalities=EQUALITIES,residuals=records,
                proof_note='../1980/EXPLORATION_DIRECT_HISTORY_LENGTH.md',
                scope='Exact same finite moving-frame Rule110 endpoint relation as round42, with direct total length replacing its square-root parameter. No universal input or halt interface is established.')


if __name__ == '__main__':
    result = verify_certificate()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['arithmetic_status'],result['operations'],result['primitive_histogram'])
    print('Finite-history improvement only; the proved universal bound remains 90.')
