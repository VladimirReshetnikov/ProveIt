#!/usr/bin/env python3
"""Exact74 bounded native ternary increment history with parity-free kernel."""
from pathlib import Path
import json
import sympy as sp

import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_parity_free_pell_kernel as kernel
import explore_native_ternary_history as old
from explore_native_ternary_ripple import decode, native, central_valuation

PARAMETERS=['FI','FF']
OUTER_NAMES=['q','FA','FB','FD','FE','FC','Jrep','alpha','W','H','v','alphaI']
CORE_NAMES=old.CORE_NAMES+['u']
SYM={name:sp.Symbol(name) for name in PARAMETERS+OUTER_NAMES+CORE_NAMES}
PREFIX=[row for row in old.PREFIX[:20] if row[0]!='q_minus_one']+old.PREFIX[20:27]+[('packed','+','FC','pack6')]
MASK=[('q2','*','q','q'),('q4','*','q2','q2'),('D0','*','q4','q')]
SCHEDULE=PREFIX+MASK+kernel.SCHEDULE
EQUALITIES=old.EQUALITIES[:10]+kernel.EQUALITIES
EQUALITIES[6]=('row_mask_product','twice_J')


def source_residuals():
    z=SYM
    FI,FF=[z[n] for n in PARAMETERS]
    q,A,B,Dw,Ew,Cw,J,alpha,W,H,v,alphaI=[z[n] for n in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[n] for n in old.CORE_NAMES]
    u=z['u'];P0=Cw+q*A+q*q*B+q**3*Dw+q**4*Ew
    scale=q**5;U,Y=w*scale,s*scale;Q=U*Y*Y;disc=a*a+6*a+8
    return [
        q-2*J-1,Ew+J-2*Dw-H,Cw+J-Dw-Ew,A+Ew-B-Dw,
        A+Ew+alpha-q-J,q-W*v,H*(W-1)-q+1,
        FI+W*B-A-q*FF,FI+alphaI-W,r-P0,
        Q*(Q+1)*k*k-tau*(tau+1),
        c-Y*k-eta,k-eta-zeta,k-r-1-h*U*Y,
        a-Y*(U+1),d-U-a*c-ga*(6*a+8),
        d*d-disc*c*c-1,(i*c*c)**2-disc*(f*f-1),
        disc*(f*f-1)*(u*u-y*y)-(1-y*y),
        u*u-(2*r+1)**2-j*c,u*u-c*c-o*f,
    ]


def verify_certificate():
    env=dict(SYM);hist=baseline.run_schedule(SCHEDULE,env)
    source=source_residuals();correction=source[17]*(SYM['u']**2-SYM['y_aux']**2)
    records=[]
    for index,((left,right),p) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        extra=source[0] if index==6 else correction if index==18 else sp.Integer(0)
        assert sp.expand(actual-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(p)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitive,counts=verify_primitives(SCHEDULE,env)
    assert len(primitive)==74 and counts=={'+':37,'*':37}
    assert len(source)==len(EQUALITIES)==len(records)==21
    assert len(OUTER_NAMES+CORE_NAMES)==30
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    used={x for row in SCHEDULE for x in row[2:]}|{x for row in EQUALITIES for x in row}
    assert set(SYM)<=used
    q=SYM['q'];J=(q-1)/2
    upper=5*J+q*((3*J-1)*(q**3+q*q)+q+1)
    assert sp.factor(3*(q**5-1)/2-upper)==(q-1)*(q+2)*(2*q*q+3*q-1)/2
    return dict(arithmetic_status='PASS',operations=74,primitive_histogram=counts,
                histogram=hist,parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=30,equations=21,primitive_instructions=primitive,
                equalities=EQUALITIES,residuals=records)


def verify_outer(z):
    # The outer nine equalities are unchanged. Check them before computing
    # the new word; the predecessor's separate scale is only a regression control.
    old.verify_outer(z)
    q=z['q'];J=z['Jrep']
    A,B,Dw,Ew,Cw=[z[n] for n in ['FA','FB','FD','FE','FC']]
    P4=A+q*B+q*q*Dw+q**3*Ew
    assert P4<=(3*J-1)*(q**3+q*q)+q+1 and Cw<5*J
    P=Cw+q*P4;scale=q**5
    assert P>q**4 and 2*P<3*(scale-1)
    assert scale>=243 and P>=83 and P<2*scale and scale<P*P
    assert scale*scale>P+1 and scale*(scale+1)>2*P+1
    assert 12*P<scale*(scale+1)
    return P


def verify_decoded(z,P):
    q=z['q'];ell=old.power_log(q,3)
    assert ell is not None and P<q**5 and P%3==2 and native(P,5*ell)
    assert all(z[n]<q and native(z[n],ell) for n in ['FC','FA','FB','FD','FE'])
    # Exact semantics are independently evaluated by the predecessor's row
    # decoder after reconstructing its native six-field control word.
    P6=z['FC']+q*z['FC']+q*q*(z['FA']+q*z['FB']+q*q*z['FD']+q**3*z['FE'])
    meaning=old.verify_decoded(z,P6)
    assert central_valuation(P)==5*ell
    return meaning


def verify_regression():
    prepower=enumerated=accepted=canonical=boundary=odd=even=0;samples=[]
    for q in range(3,64,2):
        J=(q-1)//2
        for W in range(2,q+1):
            if q%W or (q-1)%(W-1):continue
            for A in range(1,3*J):
                for Dw in range(1,3*J):
                    z=old.outer_values(q,W,A,Dw)
                    if z is None:continue
                    verify_outer(z);prepower+=1
    for ell in range(1,6):
        q=3**ell;J=(q-1)//2
        for m in range(1,ell+1):
            if ell%m:continue
            W=3**m
            for A in range(1,3*J):
                for Dw in range(1,3*J):
                    enumerated+=1
                    z=old.outer_values(q,W,A,Dw)
                    if z is None:continue
                    P=verify_outer(z)
                    if central_valuation(P)<5*ell:continue
                    meaning=verify_decoded(z,P);accepted+=1
                    if len(samples)<8:samples.append(dict(**meaning,outer=z,packed=P,parity=P%2))
    for m in range(1,9):
        for height in range(1,min(16,2**m-1)+1):
            for n in range(2**m-height):
                z,_=old.canonical(m,height,n)
                P=verify_outer(z);verify_decoded(z,P)
                canonical+=1;boundary+=z['alpha']==1;odd+=P%2;even+=P%2==0
    assert odd>0 and even>0
    return dict(prepower_positive_outer_tuples=prepower,complete_candidates=enumerated,
                accepted_complete_candidates=accepted,canonical_histories=canonical,
                canonical_alpha_one_cases=boundary,canonical_odd_indices=odd,
                canonical_even_indices=even,samples=samples,
                scope='Complete scalar candidates for total ternary widths1..5; canonical histories for widths1..8 and heights<=16; prepower positive tuples for oddq3..63. Tests explicitly include both index parities. No enormous full Pell tuple is instantiated.')


def verify():
    return dict(status='PASS_PARITY_FREE_NATIVE_TERNARY_INCREMENT_HISTORY',
                arithmetic=verify_certificate(),regression=verify_regression(),
                proof='../1980/EXPLORATION_PARITY_FREE_TERNARY_HISTORY.md',
                scope='Exact74 positive-equation relation on native ternary endpoints of nonoverflow binary increment histories. No raw numerical input conversion, machine control, halting or improved universal bound.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['regression'])
