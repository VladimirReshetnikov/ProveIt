#!/usr/bin/env python3
"""Exact62 arithmetic with a complete positive counterexample family."""
from pathlib import Path
import json
import sympy as sp
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_base_three_positive_kernel as kernel

PARAMETERS=['q','FA','FB']
OUTER_NAMES=['Hrep','FD','FC','alpha']
CORE_NAMES=kernel.CORE_NAMES
SYM={n:sp.Symbol(n) for n in PARAMETERS+OUTER_NAMES+CORE_NAMES}
PREFIX=[
    ('twice_H','+','Hrep','Hrep'),('q_rhs','+','twice_H',1),
    ('twice_D','+','FD','FD'),('local_base','+','FA','FC'),
    ('local_lhs','+','local_base','Hrep'),('local_rhs','+','FB','twice_D'),
    ('seed_lhs','+','FC','q'),('three_D','+','twice_D','FD'),
    ('seed_rhs','+','three_D',2),
    ('bound','+','local_base','alpha'),('bound_rhs','+','q','Hrep'),
    ('pack0','*','q','FD'),('pack1','+','FB','pack0'),
    ('pack2','*','q','pack1'),('pack3','+','FA','pack2'),
    ('pack4','*','q','pack3'),('packed','+','FC','pack4'),
    ('q2','*','q','q'),('n2','*','q2','q2'),
]
SCHEDULE=PREFIX+kernel.CORE
EQUALITIES=[('q','q_rhs'),('seed_lhs','seed_rhs'),('local_lhs','local_rhs'),
            ('bound','bound_rhs'),('r','packed')]+kernel.EQUALITIES[1:]


def source_residuals():
    z=SYM
    q,A,B,H,Dw,Cw,alpha=[z[n] for n in PARAMETERS+OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[n] for n in CORE_NAMES]
    packed=Cw+q*A+q*q*B+q**3*Dw
    U,Y=w*q**4,s*q**4
    Q=U*Y*Y;disc=a*a+6*a+8;aux_u=2*r+1+j*c
    return [q-2*H-1,Cw+q-3*Dw-2,A+Cw+H-B-2*Dw,
            A+Cw+alpha-q-H,r-packed,
            Q*(Q+1)*k*k-tau*(tau+1),c-Y*k-eta,k-eta-zeta,
            k-r-1-h*U*Y,a-Y*(U+1),d-U-a*c-ga*(6*a+8),
            d*d-disc*c*c-1,(i*c*c)**2-disc*(f*f-1),
            disc*(f*f-1)*(aux_u*aux_u-y*y)-(1-y*y),aux_u-c-o*f]


def verify_certificate():
    env=dict(SYM)
    histogram=baseline.run_schedule(SCHEDULE,env)
    source=source_residuals()
    u=2*SYM['r']+1+SYM['j']*SYM['c']
    correction=source[12]*(u*u-SYM['y_aux']**2)
    records=[]
    for index,((left,right),residual) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        extra=correction if index==13 else sp.Integer(0)
        assert sp.expand(actual-residual-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(residual)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(primitives)==62 and counts=={'+':32,'*':30}
    assert len(records)==len(source)==len(EQUALITIES)==15
    assert len(OUTER_NAMES+CORE_NAMES)==21
    assert all(row.free_symbols<=set(SYM.values()) for row in source)
    used={x for row in SCHEDULE for x in row[2:]}|{x for row in EQUALITIES for x in row}
    assert set(SYM)<=used
    return dict(status='ARITHMETIC_PASS_REPRESENTATION_REFUTED',arithmetic_status='PASS',
                representation_status='REFUTED_BY_COMPLETE_POSITIVE_COUNTERFAMILY',
                operations=62,primitive_histogram=counts,histogram=histogram,
                parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=21,equations=15,primitive_instructions=primitives,
                equalities=EQUALITIES,residuals=records,
                proof='../1980/EXPLORATION_NATIVE_RIPPLE_UNMASKED_CARRY.md')


def vfact(n):
    answer=0
    while n:
        n//=3;answer+=n
    return answer


def is_native(n,width):
    for _ in range(width):
        n,d=divmod(n,3)
        if d not in (1,2):return False
    return n==0


def family_case(width):
    q=3**width;H=(q-1)//2
    z=dict(q=q,FA=H,FB=H+13,Hrep=H,FD=H+12,FC=H+37,alpha=H-36)
    assert min(z.values())>0
    outer=[q-2*H-1,z['FC']+q-3*z['FD']-2,
           z['FA']+z['FC']+H-z['FB']-2*z['FD'],
           z['FA']+z['FC']+z['alpha']-q-H]
    assert outer==[0]*4
    fields=(z['FC'],z['FA'],z['FB'],z['FD'])
    assert all(is_native(x,width) and x<q for x in fields)
    packed=sum(value*q**i for i,value in enumerate(fields))
    scale=q**4;r=packed
    assert is_native(packed,4*width) and packed%3==2 and packed%2==0
    valuation=vfact(2*r)-2*vfact(r)
    assert valuation==4*width
    assert scale>=243 and r>=83 and r<scale and scale<r*r
    assert scale*scale>r+1 and scale*(scale+1)>2*r+1
    assert 12*r<scale*(scale+1)
    assert z['FB']-H==13 and z['FA']-H==0
    if width==4:assert packed==27985982 and scale==43046721
    return dict(width=width,outer=z,outer_residuals=outer,P0=packed,D0=scale,r=r,
                central_binomial_valuation=valuation,wrong_binary_endpoint=[0,7],
                positive_Pell_extension='All hypotheses of the explicit general-scale even-r converse hold; the huge tuple is not materialized.')


def verify():
    result=verify_certificate()
    result['counterexamples']=[family_case(width) for width in range(4,11)]
    result['scope']='Complete source arithmetic is valid; the proposed bounded ripple semantics is refuted, even with typed native fields, full mask and a positive Pell extension. This artifact is not a new operation bound for a correct relation.'
    return result


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],result['operations'],result['primitive_histogram'],result['equations'])
    print(len(result['counterexamples']),'exact counterfamily cases')
