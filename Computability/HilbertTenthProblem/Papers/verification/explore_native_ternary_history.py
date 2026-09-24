#!/usr/bin/env python3
"""Exact76 bounded native ternary increment history; no machine/universal claim."""
from pathlib import Path
import json
import sympy as sp

import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_base_three_positive_kernel as kernel
from explore_native_ternary_ripple import code, decode, native, central_valuation

PARAMETERS=['FI','FF']
OUTER_NAMES=['q','FA','FB','FD','FE','FC','Jrep','alpha','W','H','v','alphaI']
CORE_NAMES=kernel.CORE_NAMES
SYM={name:sp.Symbol(name) for name in PARAMETERS+OUTER_NAMES+CORE_NAMES}

PREFIX=[
    ('twice_J','+','Jrep','Jrep'),('q_rhs','+','twice_J',1),
    ('seed_lhs','+','FE','Jrep'),('twice_D','+','FD','FD'),
    ('seed_rhs','+','twice_D','H'),
    ('guard_lhs','+','FC','Jrep'),('guard_rhs','+','FD','FE'),
    ('pair_lhs','+','FA','FE'),('pair_rhs','+','FB','FD'),
    ('bound_rhs','+','q','Jrep'),('bound_lhs','+','pair_lhs','alpha'),
    ('geometry_product','*','W','v'),('q_minus_one','-', 'q',1),
    ('W_minus_one','-','W',1),('row_mask_product','*','H','W_minus_one'),
    ('time_product','*','W','FB'),('time_lhs','+','FI','time_product'),
    ('final_product','*','q','FF'),('time_rhs','+','FA','final_product'),
    ('input_bound','+','FI','alphaI'),
    ('pack0','*','q','FE'),('pack1','+','FD','pack0'),
    ('pack2','*','q','pack1'),('pack3','+','FB','pack2'),
    ('pack4','*','q','pack3'),('pack5','+','FA','pack4'),
    ('pack6','*','q','pack5'),('pack7','+','FC','pack6'),
    ('pack8','*','q','pack7'),('packed','+','FC','pack8'),
]
MASK=[('q2','*','q','q'),('q4','*','q2','q2'),('n2','*','q4','q2')]
SCHEDULE=PREFIX+MASK+kernel.CORE
EQUALITIES=[
    ('q','q_rhs'),('seed_lhs','seed_rhs'),('guard_lhs','guard_rhs'),
    ('pair_lhs','pair_rhs'),('bound_lhs','bound_rhs'),
    ('q','geometry_product'),('row_mask_product','q_minus_one'),
    ('time_lhs','time_rhs'),('input_bound','W'),('r','packed'),
]+kernel.EQUALITIES[1:]


def source_residuals():
    z=SYM
    FI,FF=[z[n] for n in PARAMETERS]
    q,A,B,Dw,Ew,Cw,J,alpha,W,H,v,alphaI=[z[n] for n in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[n] for n in CORE_NAMES]
    P0=Cw+q*Cw+q*q*A+q**3*B+q**4*Dw+q**5*Ew
    scale=q**6;U,Y=w*scale,s*scale;Q=U*Y*Y
    disc=a*a+6*a+8;aux_u=2*r+1+j*c
    return [
        q-2*J-1,Ew+J-2*Dw-H,Cw+J-Dw-Ew,A+Ew-B-Dw,
        A+Ew+alpha-q-J,q-W*v,H*(W-1)-q+1,
        FI+W*B-A-q*FF,FI+alphaI-W,r-P0,
        Q*(Q+1)*k*k-tau*(tau+1),
        c-Y*k-eta,k-eta-zeta,k-r-1-h*U*Y,
        a-Y*(U+1),d-U-a*c-ga*(6*a+8),
        d*d-disc*c*c-1,(i*c*c)**2-disc*(f*f-1),
        disc*(f*f-1)*(aux_u*aux_u-y*y)-(1-y*y),aux_u-c-o*f,
    ]


def verify_certificate():
    env=dict(SYM)
    hist=baseline.run_schedule(SCHEDULE,env)
    source=source_residuals()
    u=2*SYM['r']+1+SYM['j']*SYM['c']
    correction=source[17]*(u*u-SYM['y_aux']**2)
    records=[]
    for index,((left,right),p) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        extra=correction if index==18 else sp.Integer(0)
        assert sp.expand(actual-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],
                            source=sp.sstr(sp.expand(p)),actual=sp.sstr(actual),
                            correction=sp.sstr(sp.expand(extra))))
    primitive,counts=verify_primitives(SCHEDULE,env)
    assert len(primitive)==76 and counts=={'+':39,'*':37}
    assert len(source)==len(EQUALITIES)==len(records)==20
    assert len(OUTER_NAMES+CORE_NAMES)==29
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    used={x for row in SCHEDULE for x in row[2:]}|{x for row in EQUALITIES for x in row}
    assert set(SYM)<=used
    return dict(arithmetic_status='PASS',operations=76,primitive_histogram=counts,
                histogram=hist,parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=29,equations=20,primitive_instructions=primitive,
                equalities=EQUALITIES,residuals=records)


def outer_values(q,W,A,Dw):
    if q%2==0 or W<2 or q%W or (q-1)%(W-1):return None
    J=(q-1)//2;H=(q-1)//(W-1)
    Ew=2*Dw+H-J;Cw=Dw+Ew-J;B=A+Ew-Dw
    alpha=q+J-A-Ew
    FI=(A-W*B)%q
    FF=(FI+W*B-A)//q
    if min(Ew,Cw,B,alpha,FI,FF,W-FI)<=0:return None
    return dict(q=q,W=W,H=H,v=q//W,FA=A,FB=B,FD=Dw,FE=Ew,FC=Cw,
                Jrep=J,alpha=alpha,FI=FI,FF=FF,alphaI=W-FI)


def verify_outer(z):
    q,W,H,v,A,B,Dw,Ew,Cw,J,alpha,FI,FF,alphaI=[z[n] for n in
        ['q','W','H','v','FA','FB','FD','FE','FC','Jrep','alpha','FI','FF','alphaI']]
    assert min(z.values())>0
    assert q==2*J+1 and q==W*v and H*(W-1)==q-1
    assert Ew+J==2*Dw+H and Cw+J==Dw+Ew
    S=A+Ew
    assert S==B+Dw and S+alpha==q+J
    assert FI+W*B==A+q*FF and FI+alphaI==W
    assert S<=3*J and max(A,B,Dw,Ew)<3*J and Cw<5*J
    P4=A+q*B+q*q*Dw+q**3*Ew
    assert P4<=(3*J-1)*(q**3+q*q)+q+1
    P=Cw+q*Cw+q*q*P4;scale=q**6
    assert P>q**5 and 2*P<3*(scale-1)
    assert scale>=729 and P>=83 and P<2*scale and scale<P*P
    assert scale*scale>P+1 and scale*(scale+1)>2*P+1
    assert 12*P<scale*(scale+1)
    assert P%2==0
    return P


def power_log(n,base):
    exponent=0
    while n>1 and n%base==0:n//=base;exponent+=1
    return exponent if n==1 else None


def verify_decoded(z,P):
    q,W=z['q'],z['W'];width=power_log(q,3);m=power_log(W,3)
    assert width is not None and m and width%m==0
    height=width//m;J=z['Jrep'];jrow=(W-1)//2
    assert P<q**6 and P%3==2 and native(P,6*width)
    assert all(F<q and native(F,width) for F in [z[n] for n in ['FC','FA','FB','FD','FE']])
    raw={n:z['F'+n]-J for n in ['A','B','C','D','E']}
    assert raw['C']==raw['D']+raw['E']==3*raw['D']+z['H']
    old,new=decode(z['FI']-jrow,m),decode(z['FF']-jrow,m)
    assert old is not None and new is not None
    assert 0<=old<new==old+height<2**m
    for t in range(height):
        rows={n:(raw[n]//W**t)%W for n in raw}
        n=old+t;k=0
        while (n>>k)&1:k+=1
        assert k<m
        assert rows==dict(A=code(n),B=code(n+1),C=(3**(k+1)-1)//2,
                          D=(3**k-1)//2,E=3**k)
    assert central_valuation(P)==6*width
    return dict(width=m,height=height,input_binary=old,output_binary=new)


def canonical(m,height,old):
    W=3**m;q=W**height;J=(q-1)//2;H=(q-1)//(W-1);jrow=(W-1)//2
    assert 0<=old<old+height<2**m
    raw={n:0 for n in ['A','B','C','D','E']}
    for t in range(height):
        n=old+t;k=0
        while (n>>k)&1:k+=1
        vals=dict(A=code(n),B=code(n+1),C=(3**(k+1)-1)//2,D=(3**k-1)//2,E=3**k)
        for name,value in vals.items():raw[name]+=value*W**t
    z=dict(q=q,W=W,H=H,v=q//W,Jrep=J,FI=jrow+code(old),FF=jrow+code(old+height))
    z.update({'F'+name:J+value for name,value in raw.items()})
    z['alpha']=q+J-z['FA']-z['FE'];z['alphaI']=W-z['FI']
    P=verify_outer(z);verify_decoded(z,P)
    return z,P


def verify_regression():
    prepower=enumerated=accepted=canon=boundary=0;samples=[]
    for q in range(3,64,2):
        J=(q-1)//2
        for W in range(2,q+1):
            if q%W or (q-1)%(W-1):continue
            for A in range(1,3*J):
                for Dw in range(1,3*J):
                    z=outer_values(q,W,A,Dw)
                    if z is None:continue
                    verify_outer(z);prepower+=1
    for width in range(1,6):
        q=3**width;J=(q-1)//2
        for m in range(1,width+1):
            if width%m:continue
            W=3**m
            for A in range(1,3*J):
                for Dw in range(1,3*J):
                    enumerated+=1
                    z=outer_values(q,W,A,Dw)
                    if z is None:continue
                    P=verify_outer(z)
                    if central_valuation(P)<6*width:continue
                    meaning=verify_decoded(z,P);accepted+=1
                    if len(samples)<8:samples.append(dict(**meaning,outer=z,packed=P))
    for m in range(1,9):
        for height in range(1,min(16,2**m-1)+1):
            for old in range(2**m-height):
                z,P=canonical(m,height,old);canon+=1;boundary+=z['alpha']==1
    return dict(prepower_positive_outer_tuples=prepower,complete_candidates=enumerated,
                accepted_complete_candidates=accepted,canonical_histories=canon,
                canonical_alpha_one_cases=boundary,samples=samples,
                scope='Pre-power positive outer tuples foroddq3..63; all complete scalar candidates for total widths1..5; all nonoverflow histories of widths1..8 and heights1..min(16,2^m-1). No enormous Pell tuple is materialized.')


def verify_naive_counterexample():
    z=dict(W=9,q=81,v=9,H=10,Jrep=40,FA=44,FB=67,FD=53,FE=76,
           alpha=1,FI=8,FF=7,alphaI=1)
    q=z['q'];J=z['Jrep']
    assert q==z['W']*z['v']==2*J+1
    assert z['H']*(z['W']-1)==q-1
    assert z['FE']+J==2*z['FD']+z['H']
    assert z['FA']+z['FE']==z['FB']+z['FD']
    assert z['FA']+z['FE']+z['alpha']==q+J
    assert z['FI']+z['W']*z['FB']==z['FA']+q*z['FF']
    assert z['FI']+z['alphaI']==z['W']
    P=sum(z[n]*q**i for i,n in enumerate(['FA','FB','FD','FE']))
    r=3*P+2;scale=3*q**4
    assert native(P,16) and r%2==0 and central_valuation(r)==17
    assert q**3<P<q**4 and scale<r*r and r<scale
    assert z['FA']-J==4 and z['FB']-J==27
    assert decode(z['FI']-4,2)==3 and decode(z['FF']-4,2)==2
    return dict(status='EXACT_FALSE_NAIVE72_HISTORY',outer=z,packed=P,r=r,scale=scale,
                valuation=17,encoded_transitions=['3 -> 0','0 -> 2'],
                full_positive_kernel_extension='The published even-r enlarged base-three kernel applies. No enormous Pell tuple is instantiated.')


def verify():
    return dict(status='PASS_NATIVE_TERNARY_INCREMENT_HISTORY_COMPONENT',
                arithmetic=verify_certificate(),naive72_counterexample=verify_naive_counterexample(),
                regression=verify_regression(),proof='../1980/EXPLORATION_NATIVE_TERNARY_HISTORY.md',
                scope='Exact76 positive-equation relation between native ternary encodings of endpoints of a bounded nonoverflow binary increment history. Width and positive height are existential. No raw numerical input conversion, machine control or universality is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['regression'])
