#!/usr/bin/env python3
"""Exact79 raw +/-1 history with the first row required to increment."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_parity_free_pell_kernel as kernel
import explore_raw_ternary_mixed_history as old
from explore_native_ternary_ripple import native,central_valuation

PARAMETERS=list(old.PARAMETERS);OUTER_NAMES=list(old.OUTER_NAMES);CORE_NAMES=list(old.CORE_NAMES)
SYM={n:sp.Symbol(n) for n in PARAMETERS+OUTER_NAMES+CORE_NAMES}
FIELDS=['FKp','T0','F0','T1','F1','FKm']
PREFIX=list(old.PREFIX[:22]);prior=FIELDS[-1]
for index,field in enumerate(reversed(FIELDS[:-1])):
    product_name=f'pack_product{index}';target='packed' if index==4 else f'pack_sum{index}'
    PREFIX += [(product_name,'*','q',prior),(target,'+',field,product_name)]
    prior=target
MASK=[('q2','*','q','q'),('q4','*','q2','q2'),('D0','*','q4','q2')]
SCHEDULE=PREFIX+MASK+kernel.SCHEDULE
EQUALITIES=old.EQUALITIES[:10]+[('r','packed')]+kernel.EQUALITIES


def source_residuals():
    z=SYM
    I,Fplus=z['I'],z['Fplus'];q,J,W,H,T=z['q'],z['Jrep'],z['W'],z['H'],z['T']
    F0,F1,T0,T1,Kp,Km=[z[n] for n in ['F0','F1','T0','T1','FKp','FKm']]
    S=F0+F1;P=sum(z[n]*q**i for i,n in enumerate(FIELDS));scale=q**6
    subs={kernel.SYM[n]:z[n] for n in CORE_NAMES};subs[kernel.SYM['D0']]=scale
    return [q-2*J-1,S+z['alpha']-q-J,T0-F0-T,T1-F1-T,q-W*z['v'],
        H*(W-1)-q+1,Kp+Km-2*J-H,3*T-2*J-H,
        I+(W-1)*(S-2*J)+W*(Kp-Km)+q-q*Fplus,
        I+z['alphaI']-W,z['r']-P]+[p.subs(subs,simultaneous=True) for p in kernel.source_residuals()]


def verify_certificate():
    env=dict(SYM);hist=baseline.run_schedule(SCHEDULE,env);source=source_residuals();records=[]
    for index,((left,right),p) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        extra=source[0] if index==5 else source[18]*(SYM['u']**2-SYM['y_aux']**2) if index==19 else 0
        assert sp.expand(actual-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(p)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitive,counts=verify_primitives(SCHEDULE,env)
    assert len(primitive)==79 and counts=={'+':39,'*':40}
    assert len(source)==len(EQUALITIES)==22 and len(OUTER_NAMES+CORE_NAMES)==32
    used={x for row in SCHEDULE for x in row[2:]}|{x for pair in EQUALITIES for x in pair}
    assert set(SYM)<=used and all(p.free_symbols<=set(SYM.values()) for p in source)
    q=SYM['q'];J=(q-1)/2
    upper=1+(3*J-1)*q**5+q+q*q+(3*J-1)*(q**3+q**4)+J*(q+q**3)
    gap=sp.factor(3*(q**6-1)/2-upper)
    expected=(q-1)*(2*q**4+3*q**3+9*q*q+6*q+5)/2
    assert sp.expand(gap-expected)==0
    return dict(arithmetic_status='PASS',operations=79,primitive_histogram=counts,histogram=hist,
        parameters=PARAMETERS,parameter_domains={'I':'nonnegative raw integer','Fplus':'positive integer; raw output is Fplus-1'},
        positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=32,equations=22,
        primitive_instructions=primitive,equalities=EQUALITIES,residuals=records,packing_upper_gap=sp.sstr(gap))


def verify_outer(z):
    old.verify_outer(z)
    q=z['q'];J=z['Jrep'];P=sum(z[n]*q**i for i,n in enumerate(FIELDS));scale=q**6
    upper=1+(3*J-1)*q**5+q+q*q+(3*J-1)*(q**3+q**4)+J*(q+q**3)
    assert q**5<P<=upper and 2*P<3*(scale-1)
    assert scale>=81 and P>=27 and P<2*scale and scale<P*P
    assert scale*scale>P+1 and scale*(scale+1)>2*P+1 and 12*P<scale*(scale+1)
    return P


def verify_decoded(z,P):
    q=z['q'];ell=old.power_log(q,3)
    assert ell and P<q**6 and P%3==2 and native(P,6*ell)
    assert all(z[n]<q and native(z[n],ell) for n in FIELDS)
    assert z['FKp']%3==2 and (z['FKp']-z['Jrep'])%3==1
    priorP=sum(z[n]*q**i for i,n in enumerate(old.FIELDS));priorR=3*priorP+2
    rows=old.verify_decoded(z,priorP,priorR)
    assert rows[0]['delta']==1 and central_valuation(P)==6*ell
    return rows


def verify_regression():
    preliminary=candidates=accepted=canonical=zero_input=zero_output=final_top=odd=even=negative_first_controls=0
    samples=[]
    for q in range(3,22,2):
        J=(q-1)//2
        for W in range(2,q+1):
            if q%W or (q-1)%(W-1):continue
            H=(q-1)//(W-1)
            if (2*J+H)%3:continue
            for F0 in range(1,3*J):
                for F1 in range(1,3*J-F0+1):
                    for Kp in range(1,2*J+H):
                        z=old.outer_values(q,W,F0,F1,Kp)
                        if z is None:continue
                        verify_outer(z);preliminary+=1
    for ell in range(1,4):
        q=3**ell;J=(q-1)//2
        for m in range(1,ell+1):
            if ell%m:continue
            W=3**m;H=(q-1)//(W-1)
            for F0 in range(1,3*J):
                for F1 in range(1,3*J-F0+1):
                    for Kp in range(1,2*J+H):
                        candidates+=1
                        z=old.outer_values(q,W,F0,F1,Kp)
                        if z is None:continue
                        P=verify_outer(z)
                        if central_valuation(P)<6*ell:continue
                        rows=verify_decoded(z,P);accepted+=1
                        if len(samples)<8:samples.append(dict(outer=z,rows=rows,packed=P))
    for m in range(1,6):
        cap=3**(m-1)
        for height in range(1,5):
            for controls in product((-1,1),repeat=height):
                for initial in range(cap):
                    current=initial;valid=True
                    for delta in controls:
                        if not 0<=current<cap or current+delta<0:valid=False;break
                        current+=delta
                    if not valid:continue
                    z,_,_=old.canonical(m,controls,initial);P=verify_outer(z)
                    if controls[0]==-1:
                        assert central_valuation(P)<6*old.power_log(z['q'],3)
                        negative_first_controls+=1;continue
                    verify_decoded(z,P);canonical+=1;zero_input+=initial==0;zero_output+=current==0
                    final_top+=current==cap;odd+=P%2;even+=P%2==0
    assert zero_input and zero_output and final_top and odd and even and negative_first_controls
    return dict(prepower_positive_tuples=preliminary,complete_candidates=candidates,
        accepted_complete_candidates=accepted,canonical_first_plus_histories=canonical,
        zero_input_histories=zero_input,zero_output_histories=zero_output,
        final_at_row_guard_limit=final_top,odd_indices=odd,even_indices=even,
        rejected_first_minus_canonical_histories=negative_first_controls,samples=samples,
        scope='Complete bounded scalar candidates and direct canonical raw counter histories; both index parities, zero endpoints, last-row guard boundary and rejected first-minus controls. Full large Pell tuples exist by theorem, not numerical instantiation.')


def verify():
    return dict(status='PASS_FIRST_PLUS_RAW_TERNARY_COUNTER_HISTORY',arithmetic=verify_certificate(),
        regression=verify_regression(),proof='../1980/EXPLORATION_FIRST_PLUS_RAW_TERNARY_HISTORY.md',
        scope='Exact79 raw nonnegative mixed +/-1 history whose first step is+1. Directrawinput andpositiveoutputadapter included. Program routing, branch tests and universality remain separate.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['regression'])
