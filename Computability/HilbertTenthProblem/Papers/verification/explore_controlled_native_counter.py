#!/usr/bin/env python3
"""Exact controlled increment/hold histories:82 operations; no universal claim."""
from pathlib import Path
import itertools
import json
import sympy as sp

import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_parity_free_pell_kernel as kernel
from explore_native_ternary_ripple import code, decode, native, central_valuation
from explore_native_ternary_history import power_log

PARAMETERS=['FI','FF']
OUTER_NAMES=['q','FA','FB','FD','FE','FG','FK','FKbar','Jrep','alpha','W','H','v','alphaI']
CORE_NAMES=['a','c','d','f','h','i','j','k','o','r','s','w','tau','eta','zeta','ga','y_aux','u']
SYM={n:sp.Symbol(n) for n in PARAMETERS+OUTER_NAMES+CORE_NAMES}
FIELDS=['FG','FA','FB','FD','FE','FK','FKbar']
PREFIX=[
    ('twice_J','+','Jrep','Jrep'),('q_rhs','+','twice_J',1),
    ('seed_lhs','+','FE','twice_J'),('twice_D','+','FD','FD'),
    ('seed_rhs','+','twice_D','FK'),
    ('guard_lhs','+','FG','twice_J'),('thrice_D','+','twice_D','FD'),
    ('guard_rhs','+','thrice_D','H'),
    ('pair_lhs','+','FA','FE'),('pair_rhs','+','FB','FD'),
    ('bound_rhs','+','q','Jrep'),('bound_lhs','+','pair_lhs','alpha'),
    ('geometry_product','*','W','v'),('W_minus_one','-','W',1),
    ('row_mask_product','*','H','W_minus_one'),
    ('time_product','*','W','FB'),('time_lhs','+','FI','time_product'),
    ('final_product','*','q','FF'),('time_rhs','+','FA','final_product'),
    ('input_bound','+','FI','alphaI'),
    ('head_lhs','+','FK','FKbar'),('head_rhs','+','twice_J','H'),
]
prior=FIELDS[-1]
for index,field in enumerate(reversed(FIELDS[:-1])):
    product=f'pack_product{index}';target='packed' if index==5 else f'pack_sum{index}'
    PREFIX += [(product,'*','q',prior),(target,'+',field,product)]
    prior=target
MASK=[('q2','*','q','q'),('q3','*','q2','q'),('q4','*','q2','q2'),('D0','*','q4','q3')]
SCHEDULE=PREFIX+MASK+kernel.SCHEDULE
EQUALITIES=[('q','q_rhs'),('seed_lhs','seed_rhs'),('guard_lhs','guard_rhs'),
            ('pair_lhs','pair_rhs'),('bound_lhs','bound_rhs'),('q','geometry_product'),
            ('row_mask_product','twice_J'),('time_lhs','time_rhs'),('input_bound','W'),
            ('head_lhs','head_rhs'),('r','packed')]+kernel.EQUALITIES


def source_residuals():
    z=SYM;q,J=z['q'],z['Jrep'];W,H=z['W'],z['H']
    A,B,Dw,Ew,G,K,Kbar=[z[n] for n in ['FA','FB','FD','FE','FG','FK','FKbar']]
    scale=q**7;P=sum(z[n]*q**i for i,n in enumerate(FIELDS))
    core=kernel.source_residuals()
    subs={kernel.SYM[n]:z[n] for n in CORE_NAMES}
    subs[kernel.SYM['D0']]=scale
    return [q-2*J-1,Ew+2*J-2*Dw-K,G+2*J-3*Dw-H,
            A+Ew-B-Dw,A+Ew+z['alpha']-q-J,q-W*z['v'],H*(W-1)-q+1,
            z['FI']+W*B-A-q*z['FF'],z['FI']+z['alphaI']-W,
            K+Kbar-2*J-H,z['r']-P]+[p.subs(subs,simultaneous=True) for p in core]


def verify_certificate():
    env=dict(SYM);hist=baseline.run_schedule(SCHEDULE,env);source=source_residuals();records=[]
    for index,((left,right),poly) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        extra=source[0] if index==6 else source[18]*(SYM['u']**2-SYM['y_aux']**2) if index==19 else 0
        assert sp.expand(actual-poly-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(poly)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitive,counts=verify_primitives(SCHEDULE,env)
    assert len(primitive)==82 and counts=={'+':42,'*':40}
    assert len(source)==len(EQUALITIES)==22 and len(OUTER_NAMES+CORE_NAMES)==32
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    q=SYM['q'];J=(q-1)/2
    P4bound=(3*J-1)*(q**3+q*q)+q+1
    upper=sp.Rational(13,2)*J+q*P4bound+q**5+(3*J-1)*q**6
    gap=sp.factor(3*(q**7-1)/2-upper)
    assert sp.Poly(sp.expand(gap.subs(q,sp.Symbol('t')+3)),sp.Symbol('t')).all_coeffs()[-1]>0
    assert all(c>0 for c in sp.Poly(sp.expand(gap.subs(q,sp.Symbol('t')+3)),sp.Symbol('t')).all_coeffs())
    return dict(status='PASS',operations=82,primitive_histogram=counts,histogram=hist,
                parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=32,
                equations=22,primitive_instructions=primitive,equalities=EQUALITIES,residuals=records,
                upper_bound_gap=sp.sstr(gap),gap_coefficients_at_q_equals_t_plus_3=sp.Poly(sp.expand(gap.subs(q,sp.Symbol('t')+3)),sp.Symbol('t')).all_coeffs())


def outer_values(q,W,A,Dw,K):
    if q%2==0 or W<2 or q%W or (q-1)%(W-1):return None
    J=(q-1)//2;H=(q-1)//(W-1)
    Ew=2*Dw+K-2*J;G=3*Dw+H-2*J;Kbar=2*J+H-K;B=A+Ew-Dw
    alpha=q+J-A-Ew;FI=(A-W*B)%q;FF=(FI+W*B-A)//q
    if min(Ew,G,Kbar,B,alpha,FI,FF,W-FI)<=0:return None
    return dict(q=q,W=W,H=H,v=q//W,FA=A,FB=B,FD=Dw,FE=Ew,FG=G,FK=K,FKbar=Kbar,
                Jrep=J,alpha=alpha,FI=FI,FF=FF,alphaI=W-FI)


def verify_outer(z):
    q,W,H,J=[z[n] for n in ['q','W','H','Jrep']]
    A,B,Dw,Ew,G,K,Kbar=[z[n] for n in ['FA','FB','FD','FE','FG','FK','FKbar']]
    assert min(z.values())>0
    assert q==2*J+1 and q==W*z['v'] and H*(W-1)==q-1 and W>=3 and H<=J
    assert Ew+2*J==2*Dw+K and G+2*J==3*Dw+H
    assert A+Ew==B+Dw and A+Ew+z['alpha']==q+J and K+Kbar==2*J+H
    assert z['FI']+W*B==A+q*z['FF'] and z['FI']+z['alphaI']==W
    assert max(A,B,Dw,Ew,K,Kbar)<3*J and 2*G<13*J and 2*Dw<=5*J-2
    P=sum(z[n]*q**i for i,n in enumerate(FIELDS));scale=q**7
    assert P>q**6 and 2*P<3*(scale-1)
    assert scale>=81 and P>=27 and P<2*scale and scale<P*P
    return P


def verify_decoded(z,P):
    q,W,J,H=[z[n] for n in ['q','W','Jrep','H']]
    ell=power_log(q,3);m=power_log(W,3)
    assert ell is not None and m and ell%m==0
    height=ell//m;jrow=(W-1)//2
    assert P<q**7 and P%3==2 and native(P,7*ell)
    assert all(z[n]<q and native(z[n],ell) for n in set(FIELDS))
    raw={n:z['F'+n]-J for n in ['A','B','D','E','G','K','Kbar']}
    assert raw['K']+raw['Kbar']==H and raw['G']==3*raw['D']+H
    assert raw['E']==2*raw['D']+raw['K'] and raw['A']+raw['E']==raw['B']+raw['D']
    old=decode(z['FI']-jrow,m);final=decode(z['FF']-jrow,m)
    assert old is not None and final is not None
    n=old;controls=[]
    for t in range(height):
        rows={name:(value//W**t)%W for name,value in raw.items()}
        active=rows['K'];assert active in (0,1) and rows['Kbar']==1-active
        controls.append(active);k=0
        if active:
            while (n>>k)&1:k+=1
            assert k<m
        D=(3**k-1)//2 if active else 0;E=3**k if active else 0
        assert rows==dict(A=code(n),B=code(n+active),D=D,E=E,G=3*D+1,K=active,Kbar=1-active)
        n+=active
    assert n==final and central_valuation(P)==7*ell
    return dict(width=m,height=height,input_binary=old,output_binary=final,controls=controls)


def canonical(m,controls,old):
    height=len(controls);W=3**m;q=W**height;J=(q-1)//2;H=(q-1)//(W-1);jrow=(W-1)//2
    assert 0<=old<=old+sum(controls)<2**m
    raw={name:0 for name in ['A','B','D','E','G','K','Kbar']};n=old
    for t,active in enumerate(controls):
        k=0
        if active:
            while (n>>k)&1:k+=1
            assert k<m
        D=(3**k-1)//2 if active else 0;E=3**k if active else 0
        rows=dict(A=code(n),B=code(n+active),D=D,E=E,G=3*D+1,K=active,Kbar=1-active)
        for name,value in rows.items():raw[name]+=value*W**t
        n+=active
    z=dict(q=q,W=W,H=H,v=q//W,Jrep=J,FI=jrow+code(old),FF=jrow+code(n))
    z.update({'F'+name:J+value for name,value in raw.items()})
    z['alpha']=q+J-z['FA']-z['FE'];z['alphaI']=W-z['FI']
    P=verify_outer(z);verify_decoded(z,P);return z,P


def verify_regression():
    prepower=candidates=accepted=canonical_count=hold=alpha_one=0;samples=[]
    for q in range(3,32,2):
        J=(q-1)//2
        for W in range(3,q+1,2):
            if q%W or (q-1)%(W-1):continue
            H=(q-1)//(W-1)
            for A,Dw,K in itertools.product(range(1,3*J),range(1,3*J),range(1,2*J+H)):
                z=outer_values(q,W,A,Dw,K)
                if z is None:continue
                P=verify_outer(z);prepower+=1
                ell=power_log(q,3)
                if ell is None:continue
                candidates+=1
                if central_valuation(P)<7*ell:continue
                meaning=verify_decoded(z,P);accepted+=1
                if len(samples)<8:samples.append(dict(**meaning,outer=z))
    for m in range(1,6):
        for height in range(1,6):
            for controls in itertools.product((0,1),repeat=height):
                for old in range(max(0,2**m-sum(controls))):
                    z,P=canonical(m,controls,old)
                    canonical_count+=1;hold+=sum(controls)==0;alpha_one+=z['alpha']==1
    # Replacing the independent row guard by the ordinary C=D+E guard
    # permits a carry from the active first row into the inactive second.
    q=81;J=40;raw=dict(A=4,B=9,D=4,E=9,G=13,K=1,Kbar=9)
    bad=dict(q=q,W=9,H=10,v=9,Jrep=J,FI=8,FF=5,alphaI=1)
    bad.update({'F'+n:J+v for n,v in raw.items()});bad['alpha']=q+J-bad['FA']-bad['FE']
    assert raw['G']==raw['D']+raw['E']==3*raw['D']+raw['K']
    assert bad['FE']+2*J==2*bad['FD']+bad['FK']
    assert bad['FA']+bad['FE']==bad['FB']+bad['FD']
    assert bad['FA']+bad['FE']+bad['alpha']==q+J
    assert bad['FK']+bad['FKbar']==2*J+bad['H']
    assert bad['FI']+bad['W']*bad['FB']==bad['FA']+q*bad['FF']
    P=sum(bad[n]*q**i for i,n in enumerate(FIELDS));scale=q**7
    assert native(P,28) and P%3==2 and central_valuation(P)==28
    assert scale>=81 and P>=27 and P<2*scale and scale<P*P
    assert bad['FG']+2*J!=3*bad['FD']+bad['H']
    return dict(prepower_positive_tuples=prepower,power_three_complete_outer_candidates=candidates,
                accepted_complete_candidates=accepted,canonical_histories=canonical_count,
                all_hold_histories=hold,canonical_alpha_one=alpha_one,samples=samples,
                naive_guard_counterexample=dict(outer=bad,packed=P,scale=scale,valuation=28,
                    wrong_rows=[[3,0],[0,1]],intended_controls=[1,0],
                    full_positive_extension='All fields native, direct-unit-two divisibility and general-scale bounds give the parity-free positive Pell converse. The valid guard fails.'),
                scope='Finite outer tests supplement the general proof; no enormous Pell witnesses or universal-machine claim.')


def verify():
    return dict(status='PASS_CONTROLLED_NATIVE_INCREMENT_HOLD_HISTORY',arithmetic=verify_certificate(),
                regression=verify_regression(),proof='../1980/EXPLORATION_CONTROLLED_NATIVE_COUNTER.md',
                scope='Exact bounded native counter histories with a typed row-head activation output; raw loading, zero branches and program composition remain outside the theorem.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2,default=int)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print({k:v for k,v in result['regression'].items() if k not in ('samples','naive_guard_counterexample')})
