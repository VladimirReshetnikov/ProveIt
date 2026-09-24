#!/usr/bin/env python3
"""Exact80-operation finite Rule110 history component in radix eight."""
from pathlib import Path
import json
import sympy as sp

import round43_1980_direct_history_length as previous
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

PARAMETERS=['I','F']
OUTER_NAMES=['q','v','quot','hrow','Bw','Cw','Yw','Uw','Vw','alpha','alphaI','lam']
CORE_NAMES=previous.CORE_NAMES
NAMES=PARAMETERS+OUTER_NAMES+CORE_NAMES
SYM={name:sp.Symbol(name) for name in NAMES}

OUTER=[
    ('Q2','*','q','q'),
    ('Q4','*','Q2','Q2'),
    ('Lbig','*','Q4','Q2'),
    ('n2','*','Lbig','Q4'),
    ('vq','*','v','quot'),
    ('v2','*','v','v'),
    ('W','*','v2','v'),
    ('Qm1','-','q',1),
    ('Wm1','-','W',1),
    ('row_geom','*','hrow','Wm1'),
    ('eightC','*',8,'Cw'),
    ('fifteenB','*',15,'Bw'),
    ('fourY','*',4,'Yw'),
    ('life_lhs','+','fifteenB','fourY'),
    ('twoU','*',2,'Uw'),
    ('threeV','*',3,'Vw'),
    ('life_rhs0','+','Cw','twoU'),
    ('life_rhs','+','life_rhs0','threeV'),
    ('bound','+','life_rhs','alpha'),
    ('Ibound','+','I','alphaI'),
    ('WY','*','W','Yw'),
    ('time_lhs','+','I','WY'),
    ('QF','*','q','F'),
    ('time_rhs','+','Cw','QF'),
    ('Bh','+','Bw','hrow'),
    ('pack0','*','q','Bh'),
    ('pack1','+','Yw','pack0'),
    ('pack2','*','q','pack1'),
    ('pack3','+','Vw','pack2'),
    ('pack4','*','q','pack3'),
    ('packed','+','Uw','pack4'),
    ('seven_lam','*',7,'lam'),
    ('mask_scale','+','seven_lam',1),
    ('packing_gap','-','Lbig','packed'),
    ('r_product','*','packing_gap','seven_lam'),
    ('six_lam','*',6,'lam'),
    ('r_lhs','+','r_product','six_lam'),
]
CORE=previous.CORE
SCHEDULE=OUTER+CORE
EQUALITIES=[
    ('q','vq'),('Qm1','row_geom'),('Bw','eightC'),
    ('life_lhs','life_rhs'),('bound','q'),('Ibound','v'),
    ('time_lhs','time_rhs'),('mask_scale','Lbig'),('r','r_lhs'),
]+previous.EQUALITIES[10:]


def source_residuals():
    z=SYM
    q,v,quot,H,B,C,Y,U,V,alpha,alphaI,lam=[z[name] for name in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[name] for name in CORE_NAMES]
    W,L,scale=v**3,q**6,q**10
    P=U+q*V+q*q*Y+q**3*(B+H)
    Up,Yp=w*scale,s*scale
    Dpell=a*a+4*a+3
    K,aux_u=Dpell*(f*f-1),2*r+1+j*c
    return [
        q-v*quot,
        q-1-H*(W-1),
        B-8*C,
        15*B+4*Y-C-2*U-3*V,
        C+2*U+3*V+alpha-q,
        z['I']+alphaI-v,
        z['I']+W*Y-C-q*z['F'],
        7*lam+1-L,
        r-(L-P)*7*lam-6*lam,
        Up*Yp*Yp*(Up*Yp*Yp+1)*k*k-tau*(tau+1),
        c-Yp*k-eta,
        k-eta-zeta,
        k-r-1-h*Up*Yp,
        a-Yp*(Up+1),
        d-Up-a*c-ga*(4*a+3),
        d*d-Dpell*c*c-1,
        (i*c*c)**2-Dpell*(f*f-1),
        K*(aux_u*aux_u-y*y)-(1-y*y),
        aux_u-c-o*f,
    ]


def verify_certificate():
    need=baseline.need
    need(len(OUTER)==37 and len(CORE)==43,'37 outer and43 retained instructions')
    env=dict(SYM)
    histogram=baseline.run_schedule(SCHEDULE,env)
    source=source_residuals()
    z=SYM;aux_u=2*z['r']+1+z['j']*z['c']
    correction=source[16]*(aux_u**2-z['y_aux']**2)
    records=[]
    for index,((left,right),residual) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        adjustment=correction if index==17 else sp.Integer(0)
        if sp.expand(actual-residual-adjustment)==0:
            sign=1
        elif adjustment==0 and sp.expand(actual+residual)==0:
            sign=-1
        else:
            raise AssertionError('fresh source residual mismatch at '+str(index))
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(residual)),actual=sp.sstr(actual),
                            correction=sp.sstr(sp.expand(adjustment))))
    need(len(records)==len(source)==len(EQUALITIES)==19,'19 complete source equations')
    primitives,counts=verify_primitives(SCHEDULE,env)
    need(len(primitives)==80 and counts=={'+':34,'*':46},'exact80 operations')
    need(len(OUTER_NAMES+CORE_NAMES)==29,'29 positive unknowns')
    need(all(residual.free_symbols<=set(SYM.values()) for residual in source),
         'all fresh source symbols declared')
    need(set(NAMES)<={operand for row in SCHEDULE for operand in row[2:]}|
         {operand for pair in EQUALITIES for operand in pair},'all supplied inputs used')
    need(sp.expand(env['n2']-z['q']**10)==0,'squared Pell scale q10')
    need(sp.expand(env['W']-z['v']**3)==0,'row radix v3')
    P=z['Uw']+z['q']*z['Vw']+z['q']**2*z['Yw']+z['q']**3*(z['Bw']+z['hrow'])
    need(sp.expand(env['packed']-P)==0,'four-field packed word')
    return dict(status='ARITHMETIC_PASS_FOR_TWO_AUXILIARY_HISTORY',
                arithmetic_status='PASS',universality_status='NOT_ESTABLISHED',
                operations=80,histogram=histogram,primitive_histogram=counts,
                parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=29,equations=19,outer_operations=37,
                retained_pell_operations=43,radix=8,
                packing='U+qV+q^2Y+q^3(B+H)',
                local_equation='15B+4Y=C+2U+3V',
                shared_bound='C+2U+3V+alpha=q',
                squared_pell_scale='q^10',
                primitive_instructions=primitives,equalities=EQUALITIES,residuals=records,
                proof_note='../1980/EXPLORATION_TWO_AUXILIARY_HISTORY.md',
                scope='Finite zero-exterior moving-frame Rule110 histories in radix eight, with two local auxiliary planes and explicit output Booleanity. The positive endpoint relation has no111-filter. A separate proof establishes the semantics; no universal input or halt interface is claimed.')


if __name__=='__main__':
    result=verify_certificate()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['arithmetic_status'],result['operations'],result['primitive_histogram'])
    print(result['unknown_count'],'positive unknowns;',result['equations'],'equations')
    print('Finite-history component only; no universal operation bound is claimed.')
