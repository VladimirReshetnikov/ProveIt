#!/usr/bin/env python3
"""Full positive counterexample to periodicizing the derived-D ripple."""
from pathlib import Path
import json
import sympy as sp
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_parity_free_pell_kernel as kernel
import explore_native_ternary_history as history
from explore_native_ternary_ripple import native,decode,central_valuation

PARAMETERS=['FI','FF']
OUTER_NAMES=['q','FA','FB','FC','FE','Jrep','alpha','W','H','v','alphaI']
CORE_NAMES=history.CORE_NAMES+['u']
SYM={name:sp.Symbol(name) for name in PARAMETERS+OUTER_NAMES+CORE_NAMES}
PREFIX=[
    ('twice_J','+','Jrep','Jrep'),('q_rhs','+','twice_J',1),
    ('three_E','*',3,'FE'),('twice_C','+','FC','FC'),
    ('seed_offset','+','Jrep','H'),('seed_rhs','+','twice_C','seed_offset'),
    ('S','+','FA','FE'),('local_lhs','+','S','FE'),
    ('local_pair','+','FB','FC'),('local_rhs','+','local_pair','Jrep'),
    ('bound_lhs','+','S','alpha'),('bound_rhs','+','q','Jrep'),
    ('geometry_product','*','W','v'),('W_minus_one','-','W',1),
    ('row_mask_product','*','H','W_minus_one'),
    ('time_product','*','W','FB'),('time_lhs','+','FI','time_product'),
    ('final_product','*','q','FF'),('time_rhs','+','FA','final_product'),
    ('input_bound','+','FI','alphaI'),
    ('pack0','*','q','FE'),('pack1','+','FB','pack0'),
    ('pack2','*','q','pack1'),('pack3','+','FA','pack2'),
    ('pack4','*','q','pack3'),('packed','+','FC','pack4'),
    ('q2','*','q','q'),('D0','*','q2','q2'),
]
SCHEDULE=PREFIX+kernel.SCHEDULE
EQUALITIES=[('q','q_rhs'),('three_E','seed_rhs'),('local_lhs','local_rhs'),
    ('bound_lhs','bound_rhs'),('q','geometry_product'),('row_mask_product','twice_J'),
    ('time_lhs','time_rhs'),('input_bound','W'),('r','packed')]+kernel.EQUALITIES


def source_residuals():
    z=SYM
    FI,FF=[z[n] for n in PARAMETERS]
    q,A,B,Cw,Ew,J,alpha,W,H,v,alphaI=[z[n] for n in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[n] for n in history.CORE_NAMES]
    u=z['u'];P=Cw+q*A+q*q*B+q**3*Ew
    scale=q**4;U,Y=w*scale,s*scale;Q=U*Y*Y;disc=a*a+6*a+8
    return [q-2*J-1,3*Ew-2*Cw-J-H,A+2*Ew-B-Cw-J,A+Ew+alpha-q-J,
        q-W*v,H*(W-1)-q+1,FI+W*B-A-q*FF,FI+alphaI-W,r-P,
        Q*(Q+1)*k*k-tau*(tau+1),c-Y*k-eta,k-eta-zeta,k-r-1-h*U*Y,
        a-Y*(U+1),d-U-a*c-ga*(6*a+8),d*d-disc*c*c-1,
        (i*c*c)**2-disc*(f*f-1),disc*(f*f-1)*(u*u-y*y)-(1-y*y),
        u*u-(2*r+1)**2-j*c,u*u-c*c-o*f]


def verify_certificate():
    env=dict(SYM);hist=baseline.run_schedule(SCHEDULE,env);source=source_residuals()
    correction=source[16]*(SYM['u']**2-SYM['y_aux']**2);records=[]
    for index,((left,right),p) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        extra=source[0] if index==5 else correction if index==17 else sp.Integer(0)
        assert sp.expand(actual-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(p)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitive,counts=verify_primitives(SCHEDULE,env)
    assert len(primitive)==72 and counts=={'+':36,'*':36}
    assert len(source)==len(EQUALITIES)==20 and len(OUTER_NAMES+CORE_NAMES)==29
    return dict(arithmetic_status='PASS_REJECTED_CANDIDATE_ONLY',operations=72,
        primitive_histogram=counts,histogram=hist,equations=20,parameters=PARAMETERS,
        positive_unknowns=OUTER_NAMES+CORE_NAMES,primitive_instructions=primitive,
        equalities=EQUALITIES,residuals=records)


def counterexample():
    z=dict(q=729,W=27,H=28,v=27,Jrep=364,FA=455,FB=475,FC=368,FE=376,
           alpha=262,FI=23,FF=17,alphaI=4)
    q=z['q'];P=z['FC']+q*z['FA']+q*q*z['FB']+q**3*z['FE'];z['r']=P
    substitutions={SYM[name]:value for name,value in z.items()}
    source=source_residuals();numeric=[int(p.subs(substitutions)) for p in source[:9]]
    assert numeric==[0]*9 and min(z.values())>0
    assert all(native(z[name],6) for name in ['FA','FB','FC','FE'])
    assert native(P,24) and P%3==2 and central_valuation(P)==24
    scale=q**4
    assert scale>=81 and P>=27 and P<2*scale and scale<P*P
    assert q**3<P<scale and z['q']==z['W']**2
    raw={name:z['F'+name]-z['Jrep'] for name in ['A','B','C','E']}
    assert raw==dict(A=91,B=111,C=4,E=12)
    assert raw['C']-raw['E']==-8
    rows=[]
    for t in range(2):
        row={name:(value//27**t)%27 for name,value in raw.items()}
        rows.append(dict(source=decode(row['A'],3),target=decode(row['B'],3),raw=row))
    assert [(row['source'],row['target']) for row in rows]==[(5,2),(2,3)]
    assert decode(z['FI']-13,3)==5 and decode(z['FF']-13,3)==3
    return dict(outer=z,numeric_source_residuals=numeric,scale=scale,
        valuation=24,index_parity=P%2,raw_fields=raw,rows=rows,
        false_endpoint='Native input encodes5 and output encodes3 at width3,height2; ordinary increments require5->6->7.',
        positive_kernel_extension='The general parity-free44 theorem applies to D0=q^4,r=P: power-of-three scale, exact valuation24, D0>=81,r>=27,r<2D0,D0<r^2. It constructs all17 remaining positive Pell auxiliaries including u. The enormous tuple is not materialized.')


def verify():
    return dict(status='PASS_FULL_COUNTEREXAMPLE_PERIODIC_DERIVED_CARRY',
        rejected_candidate=verify_certificate(),counterexample=counterexample(),
        proof='../1980/EXPLORATION_PERIODIC_DERIVED_CARRY_COUNTEREXAMPLE.md',
        scope='Exact arithmetic and one full positive counterexample to this specific periodic-seed extension of the valid single-ripple compiler. No obstruction to every four-field history design is claimed.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['rejected_candidate']['operations'],result['rejected_candidate']['primitive_histogram'])
    print(result['counterexample'])
