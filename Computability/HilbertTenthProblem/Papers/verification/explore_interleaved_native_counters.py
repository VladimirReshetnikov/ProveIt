#!/usr/bin/env python3
"""Fixed-many interleaved increment/hold histories; exact85, not universality."""
from pathlib import Path
import itertools
import json
import sympy as sp

import explore_controlled_native_counter as old
from explore_native_ternary_ripple import native, central_valuation
from explore_native_ternary_history import power_log

FIELDS=old.FIELDS
OUTER_NAMES=old.OUTER_NAMES+['width_multiple']
SYM={name:sp.Symbol(name) for name in old.PARAMETERS+OUTER_NAMES+old.CORE_NAMES}


def schedule(pm1,jblock):
    result=[]
    for name,op,left,right in old.PREFIX:
        if name=='seed_lhs':
            result.extend([('stride_J','*',pm1,'Jrep'),('all_heads','*',jblock,'H')])
        if name in ('seed_lhs','guard_lhs'):right='stride_J'
        if name=='twice_D':op,left,right='*',pm1,'FD'
        if name=='guard_rhs':right='all_heads'
        if name=='head_rhs':right='all_heads'
        result.append((name,op,left,right))
        if name=='W_minus_one':result.append(('width_product','*',pm1,'width_multiple'))
    return result+old.MASK+old.kernel.SCHEDULE


def sources(p):
    z=SYM;J=z['Jrep'];H=z['H'];q=z['q'];W=z['W'];pm1=p-1
    sub={old.SYM[name]:z[name] for name in old.SYM}
    source=[s.subs(sub,simultaneous=True) for s in old.source_residuals()]
    source[1]=z['FE']+pm1*J-pm1*z['FD']-z['FK']
    source[2]=z['FG']+pm1*J-p*z['FD']-pm1*H/2
    source[9]=z['FK']+z['FKbar']-2*J-pm1*H/2
    return source+[W-1-pm1*z['width_multiple']]


def verify_certificate(k=2,symbolic=False):
    p=sp.Symbol('p') if symbolic else sp.Integer(3**k)
    pm1,jblock=('stride_minus_one','head_block') if symbolic else (int(p-1),int((p-1)/2))
    instructions=schedule(pm1,jblock)
    env=dict(SYM)
    if symbolic:env.update(stride_minus_one=p-1,head_block=(p-1)/2)
    hist=old.baseline.run_schedule(instructions,env)
    source=sources(p);equalities=old.EQUALITIES+[('W_minus_one','width_product')];records=[]
    for i,((left,right),poly) in enumerate(zip(equalities,source)):
        actual=sp.expand(env[left]-env[right])
        extra=source[0] if i==6 else source[18]*(SYM['u']**2-SYM['y_aux']**2) if i==19 else 0
        assert sp.expand(actual-poly-extra)==0,i
        records.append(dict(index=i,equality=[left,right],source=sp.sstr(sp.expand(poly)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitive,counts=old.verify_primitives(instructions,env)
    assert len(primitive)==85 and counts=={'+':41,'*':44}
    assert len(source)==23 and len(OUTER_NAMES+old.CORE_NAMES)==33
    assert all(s.free_symbols<=set(SYM.values())|({p} if symbolic else set()) for s in source)
    return dict(status='PASS',operations=85,primitive_histogram=counts,histogram=hist,
                fixed_counter_count='arbitrary k>=2' if symbolic else k,
                fixed_stride=sp.sstr(p),unknown_count=33,equations=23,
                positive_unknowns=OUTER_NAMES+old.CORE_NAMES,parameters=old.PARAMETERS,
                primitive_instructions=primitive,equalities=equalities,residuals=records)


def encode(values,k):
    return sum(((value>>i)&1)*3**(k*i+lane)
               for lane,value in enumerate(values) for i in range(value.bit_length()))


def decode_lanes(word,k,m):
    out=[0]*k
    for place in range(m):
        bit=word%3;word//=3
        assert bit in (0,1)
        out[place%k]+=bit<<(place//k)
    assert word==0
    return out


def outer_values(k,q,W,A,D,K):
    p=3**k;pm1=p-1
    if q%2==0 or W<p or q%W or (q-1)%(W-1) or (W-1)%pm1:return None
    J=(q-1)//2;H=(q-1)//(W-1);Ha=pm1*H//2
    E=pm1*D+K-pm1*J;G=p*D+Ha-pm1*J;Kb=2*J+Ha-K;B=A+E-D
    alpha=q+J-A-E;FI=(A-W*B)%q;FF=(FI+W*B-A)//q
    if min(E,G,Kb,B,alpha,FI,FF,W-FI)<=0:return None
    return dict(q=q,W=W,H=H,v=q//W,width_multiple=(W-1)//pm1,Jrep=J,
                FA=A,FB=B,FD=D,FE=E,FG=G,FK=K,FKbar=Kb,
                alpha=alpha,FI=FI,FF=FF,alphaI=W-FI)


def verify_outer(k,z):
    p=3**k;pm1=p-1;q,W,H,J=[z[n] for n in ['q','W','H','Jrep']];Ha=pm1*H//2
    A,B,D,E,G,K,Kb=[z[n] for n in ['FA','FB','FD','FE','FG','FK','FKbar']]
    assert min(z.values())>0
    assert q==2*J+1 and q==W*z['v'] and H*(W-1)==2*J
    assert W-1==pm1*z['width_multiple'] and W>=p and Ha<=J
    assert E+pm1*J==pm1*D+K and G+pm1*J==p*D+Ha
    assert A+E==B+D and A+E+z['alpha']==q+J and K+Kb==2*J+Ha
    assert z['FI']+W*B==A+q*z['FF'] and z['FI']+z['alphaI']==W
    assert max(A,B,D,E,K,Kb)<3*J and pm1*D<=(p+2)*J-2 and 2*G<13*J
    P=sum(z[name]*q**i for i,name in enumerate(FIELDS));scale=q**7
    assert P>q**6 and 2*P<3*(scale-1)
    assert scale>=81 and P>=27 and P<2*scale and scale<P*P
    return P


def verify_decoded(k,z,P):
    p=3**k;q,W,J,H=[z[n] for n in ['q','W','Jrep','H']]
    ell=power_log(q,3);m=power_log(W,3)
    assert ell and m and ell%m==0 and m%k==0
    height=ell//m;jrow=(W-1)//2;jblock=(p-1)//2
    assert P<q**7 and P%3==2 and native(P,7*ell)
    assert all(z[name]<q and native(z[name],ell) for name in FIELDS)
    raw={name:z['F'+name]-J for name in ['A','B','D','E','G','K','Kbar']}
    assert raw['K']+raw['Kbar']==jblock*H
    values=decode_lanes(z['FI']-jrow,k,m);initial=list(values);controls=[]
    final=decode_lanes(z['FF']-jrow,k,m)
    for time in range(height):
        rows={name:(value//W**time)%W for name,value in raw.items()}
        eps=decode_lanes(rows['K'],k,k);controls.append(eps)
        D=E=0
        for lane,(value,active) in enumerate(zip(values,eps)):
            trailing=0
            if active:
                while (value>>trailing)&1:trailing+=1
                assert trailing<m//k
                D+=3**lane*(p**trailing-1)//(p-1)
                E+=3**lane*p**trailing
        new=[value+active for value,active in zip(values,eps)]
        assert rows==dict(A=encode(values,k),B=encode(new,k),D=D,E=E,G=p*D+jblock,
                          K=encode(eps,k),Kbar=jblock-encode(eps,k))
        values=new
    assert values==final and central_valuation(P)==7*ell
    return dict(counters=k,bits_per_counter=m//k,height=height,initial=initial,final=final,controls=controls)


def canonical(k,bits,controls,initial):
    p=3**k;m=k*bits;height=len(controls);W=3**m;q=W**height;J=(q-1)//2
    H=(q-1)//(W-1);jblock=(p-1)//2;jrow=(W-1)//2
    raw={name:0 for name in ['A','B','D','E','G','K','Kbar']};values=list(initial)
    for time,eps in enumerate(controls):
        D=E=0
        for lane,(value,active) in enumerate(zip(values,eps)):
            assert active in (0,1) and 0<=value<2**bits and value+active<2**bits
            trailing=0
            if active:
                while (value>>trailing)&1:trailing+=1
                D+=3**lane*(p**trailing-1)//(p-1);E+=3**lane*p**trailing
        new=[value+active for value,active in zip(values,eps)]
        rows=dict(A=encode(values,k),B=encode(new,k),D=D,E=E,G=p*D+jblock,
                  K=encode(eps,k),Kbar=jblock-encode(eps,k))
        for name,value in rows.items():raw[name]+=value*W**time
        values=new
    z=dict(q=q,W=W,H=H,v=q//W,width_multiple=(W-1)//(p-1),Jrep=J,
           FI=jrow+encode(initial,k),FF=jrow+encode(values,k))
    z.update({'F'+name:J+value for name,value in raw.items()})
    z['alpha']=q+J-z['FA']-z['FE'];z['alphaI']=W-z['FI']
    P=verify_outer(k,z);verify_decoded(k,z,P);return z,P


def verify_regression():
    pre=candidates=accepted=canon=allhold=alphaone=0;samples=[]
    for k in (2,3):
        p=3**k
        for q in range(p,34,2):
            J=(q-1)//2
            for W in range(p,q+1,p-1):
                if q%W or (q-1)%(W-1):continue
                H=(q-1)//(W-1);Ha=(p-1)*H//2
                for A,D,K in itertools.product(range(1,3*J),range(1,3*J),range(1,2*J+Ha)):
                    z=outer_values(k,q,W,A,D,K)
                    if z is None:continue
                    P=verify_outer(k,z);pre+=1;ell=power_log(q,3)
                    if ell is None:continue
                    candidates+=1
                    if central_valuation(P)<7*ell:continue
                    meaning=verify_decoded(k,z,P);accepted+=1
                    if len(samples)<8:samples.append(meaning)
    for k,bits,height in [(2,1,1),(2,1,2),(2,2,1),(2,2,2),(2,2,3),(3,1,1),(3,1,2),(3,2,1),(3,2,2),(4,1,1),(4,1,2)]:
        for flat in itertools.product((0,1),repeat=k*height):
            controls=[flat[k*t:k*(t+1)] for t in range(height)]
            totals=[sum(row[lane] for row in controls) for lane in range(k)]
            for initial in itertools.product(*(range(2**bits-total) for total in totals)):
                z,P=canonical(k,bits,controls,initial)
                canon+=1;allhold+=not any(flat);alphaone+=z['alpha']==1
    # The tempting absorbed all-head geometry permits partial final rows.
    p=W=9;q=27;J=Ha=13
    bad=dict(q=q,W=W,J=J,H_all=Ha,A=J,B=J,D=J,E=J,K=J,G=2*J,Kbar=2*J,
             FI=4,FF=4,v=3,alpha=14,alphaI=5,width_multiple=1)
    assert Ha*(W-1)==(p-1)*J and q==W*bad['v'] and (W-1)==(p-1)*bad['width_multiple']
    assert bad['E']+(p-1)*J==(p-1)*bad['D']+bad['K']
    assert bad['G']+(p-1)*J==p*bad['D']+Ha
    assert bad['K']+bad['Kbar']==2*J+Ha and bad['A']+bad['E']==bad['B']+bad['D']
    assert bad['A']+bad['E']+bad['alpha']==q+J and bad['FI']+bad['alphaI']==W
    assert bad['FI']+W*bad['B']==bad['A']+q*bad['FF']
    P=sum(bad[name[1:]]*q**i for i,name in enumerate(FIELDS));D0=q**7
    assert native(P,21) and P%3==2 and central_valuation(P)==21
    assert D0>=81 and P>=27 and P<2*D0 and D0<P*P and power_log(q,W) is None
    return dict(prepower_positive_tuples=pre,power_three_complete_candidates=candidates,
                accepted_complete_candidates=accepted,canonical_histories=canon,
                all_hold_histories=allhold,alpha_one=alphaone,samples=samples,
                partial_row_counterexample=dict(outer=bad,packed=P,scale=D0,valuation=21,
                    scope='Refutes the proposed exact q=W^t geometry; its all-hold endpoints themselves are valid. Full parity-free positive Pell extension applies.'),
                scope='Finite cases supplement the general proof. No universal machine or raw-number loader is asserted.')


def verify():
    generic=verify_certificate(symbolic=True)
    arithmetic=verify_certificate()
    return dict(status='PASS_INTERLEAVED_NATIVE_COUNTER_HISTORIES',arithmetic=arithmetic,
                symbolic_coefficient_template=dict(status=generic['status'],operations=generic['operations'],equations=generic['equations']),
                regression=verify_regression(),proof='../1980/EXPLORATION_INTERLEAVED_NATIVE_COUNTERS.md')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2,default=int)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print({k:v for k,v in result['regression'].items() if k not in ('samples','partial_row_counterexample')})
