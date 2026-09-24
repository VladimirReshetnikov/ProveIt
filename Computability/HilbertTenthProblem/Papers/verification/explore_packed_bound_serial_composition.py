#!/usr/bin/env python3
"""Exact115: bound the packed certificate instead of program fields."""
from pathlib import Path
import json
import sympy as sp
import explore_complement_zero_serial_composition as old
from explore_native_ternary_ripple import native, central_valuation

SYM=old.SYM
PROGRAM=old.PROGRAM
FIELDS=old.FIELDS
OUTER_NAMES=old.OUTER_NAMES
CORE_NAMES=old.CORE_NAMES


def build():
    previous,pairs,source=old.build()
    ops=[]
    for name,op,left,right in previous:
        if name in ('program_bound_sum','combined_sum'):
            continue
        if name=='program_bound':
            left,right='r','beta'
        ops.append((name,op,left,right))
    pairs=list(pairs);pairs[24]=('program_bound','D0')
    source=list(source);source[24]=SYM['r']+SYM['beta']-SYM['q']**12
    return ops,pairs,source


def verify_certificate():
    ops,pairs,source=build();env=dict(SYM)
    old.old.old.old.old.aligned.baseline.run_schedule(ops,env)
    primitives,counts=old.old.old.old.old.aligned.verify_primitives(ops,env)
    assert len(primitives)==115 and counts=={'+':59,'*':56}
    assert len(source)==len(pairs)==31 and len(OUTER_NAMES+CORE_NAMES)==43
    previous=old.build()[2]
    u=SYM['j']*SYM['c']+2*SYM['r']+1
    records=[]
    for i,((left,right),polynomial) in enumerate(zip(pairs,source)):
        correction=source[17]*(u*u-SYM['y_aux']**2) if i==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-correction)==0,i
        if i!=24:
            assert polynomial==previous[i]
        records.append(dict(index=i,equality=[left,right],source=sp.sstr(polynomial),
                            correction=sp.sstr(correction)))
    c=PROGRAM
    assert c['K']>=3 and c['S']>=c['I']>=1 and c['Rmin']>c['g']*c['S']
    assert c['Rmin']>12*(c['K']*c['S']+old.ZALL+1)
    return dict(operations=115,primitive_histogram=counts,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=43,equations=31,primitive_instructions=primitives,
                equalities=pairs,residuals=records,
                delta=dict(removed=['program_bound_sum','combined_sum'],
                           replacement='program_bound=r+beta; compare with D0',
                           unchanged_source_count=30),
                scope='Exact full source and primitive schedule; the mathematical decoding proof is separate.')


def verify_carry_lemmas():
    guard_cases=valid_pairs=0
    # This tests the guard/base recovery lemma over its full finite domain,
    # including deliberately overflowing supplied fields.
    for ell in range(1,7):
        q=3**ell;J=(q-1)//2
        allowed=[native(n,ell) for n in range(q)]
        for F in range(1,3*J):
            for T in range(1,J+1):
                G=F+T;carry,rem=divmod(G,q)
                nextcarry,baserem=divmod(F+carry,q)
                if allowed[rem] and allowed[baserem]:
                    assert carry==nextcarry==0
                    assert native(F,ell) and native(G,ell)
                    valid_pairs+=1
                guard_cases+=1
    # Verify the potentially large guard carries before T is recovered.
    coarse_cases=0
    for R in (9,27,81):
        for u in (3,4):
            q=R**u;J=(q-1)//2;H=(q-1)//(R-1)
            tmax=((R+3)*J-1)//6
            assert 3*J+tmax+1<R*q and 3*J+R-1<2*q
            assert J+H+1<q and 2*J+H<q+J
            for F in (1,J-1,J,q-1,q,3*J-2,3*J-1):
                for T in (1,J,tmax):
                    for incoming in (0,1):
                        assert (F+T+incoming)//q<=R-1
                        for carry in (0,1,R-2,R-1):
                            assert (F+carry)//q<=1
                            coarse_cases+=1
    # Exact polynomial certificates for the two scalar inequalities, valid
    # for every R>=9, J>=1 and q>=R^3, not merely sampled powers.
    rr,jj,vv=sp.symbols('rr jj vv',nonnegative=True)
    R=9+rr;J=1+jj
    polys=[sp.expand(6*R*(2*J+1)-(R+21)*J-6),
           sp.expand(R**3*(1+vv)+3-2*R)]
    for p in polys:
        assert all(coef>0 for coef in sp.Poly(p,rr,jj,vv).coeffs())
    return dict(guard_base_assignments=guard_cases,accepted_native_pairs=valid_pairs,
                coarse_carry_extremes=coarse_cases,
                nonnegative_coefficient_identities=[sp.sstr(p) for p in polys],
                scope='Exhaustive finite guard/base assignments plus general polynomial inequalities; not an exhaustive full-system search.')


def canonical(x):
    c=PROGRAM;path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0]
    blocks=len(path)-1;R=c['Rmin'];W=R**3;q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1)
    values=[2*x,0,0];A0=A1=Kp=Km=Z=0
    for b,state in enumerate(path[:-1]):
        lane=b%3
        assert c['phases'][state]==lane and (state,path[b+1]) in c['edges']
        n=values[lane];assert 0<=n<R//3
        if c['zeros'][state]:assert n==0
        first,second=old.old.old.old.old.aligned.single.split_ternary(n,b)
        weight=R**b;A0+=first*weight;A1+=second*weight
        if c['signs'][state]==1:Kp+=weight
        else:Km+=weight
        Z+=c['zeros'][state]*weight
        last=(n,c['signs'][state],c['zeros'][state])
        values[lane]+=c['signs'][state]
        assert min(values)>=0
    assert values==[0,0,0] and blocks%6==0 and last==(1,-1,0)
    D=H-Z;T=J-((R-3)//6)*D
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*Kp-c['hz']*D
    TC=C+J-c['S']*H;TV=V+old.ZALL*H
    z=dict(x=x,q=q,Jrep=J,R=R,W=W,H=H,v=q//W,T=T,
           F0=J+A0,F1=J+A1,G0=J+A0+T,G1=J+A1+T,FKplus=J+Kp,FKminus=J+Km,
           FZ=J+Z,FZbar=J+D,alphaI=R-2*x,PC=C,PV=V,PTC=TC,PTV=TV,
           PNC=J+C,PNV=J+V,PNTC=J+TC,PNTV=J+TV,zR=1)
    P=sum(z[n]*q**i for i,n in enumerate(FIELDS));z['r']=P;z['beta']=q**12-P
    assert min(z.values())>0
    source=build()[2];indices=list(range(10))+list(range(20,31))
    sub={SYM[name]:value for name,value in z.items()}
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in indices)
    oldbeta=q-T-TC-TV
    assert oldbeta>0 and q-T-TC-TV==oldbeta
    restored=dict(sub);restored[SYM['beta']]=oldbeta
    assert all(old.build()[2][i].subs(restored,simultaneous=True)==0 for i in indices)
    ell=c['B']*blocks
    assert all(native(z[n],ell) and z[n]<q for n in FIELDS)
    assert native(P,12*ell) and P%3==2 and P%2==0 and q**11<P<q**12<P*P
    valuation=central_valuation(P);assert valuation==12*ell
    assert 0<V<TV<=J and C<q and V+c['hs']*Kp+c['hz']*D<q
    return dict(x=x,serial_blocks=blocks,counter_width=c['B'],outer_residuals=len(indices),
                restored_117_outer_residuals=len(indices),positive_new_and_old_slacks=True,
                packed_bits=P.bit_length(),valuation=valuation,
                scope='Full unchanged canonical path, all12 native fields, all21 new and restored outer sources, parity and kernel bounds. The proved converse supplies unmaterialized enormous Pell coordinates.')


def verify():
    return dict(status='PASS_PACKED_BOUND_SERIAL_COMPOSITION_115',
                arithmetic=verify_certificate(),carry_lemmas=verify_carry_lemmas(),
                canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_PACKED_BOUND_SERIAL_COMPOSITION.md',
                scope='Complete115-operation universal family; independent full proof/source audits and fresh verification pass. The established universal frontier remains90.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['carry_lemmas']);print(result['canonical'])
