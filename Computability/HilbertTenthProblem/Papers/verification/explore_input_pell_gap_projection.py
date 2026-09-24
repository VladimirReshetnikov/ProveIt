#!/usr/bin/env python3
"""Exact projection after deleting input Pell gap; no universal80 claim."""
from pathlib import Path
from math import gcd,lcm,comb
import json
import sys
import sympy as sp

import explore_fixed_raw_universal_81 as base

OUT=Path(__file__).with_suffix('.json')
NAMES=[name for name in base.NAMES if name!='phi']
SYM={name:sp.Symbol(name) for name in NAMES+base.CONSTANTS+['x']}
SCHEDULE=[row for row in base.SCHEDULE if row[0]!='pell_gap']
EQUALITIES=[pair for pair in base.EQUALITIES if pair!=('c','pell_gap')]


def verify_source():
    env=base.fixed_environment(SYM);base.bridge.baseline.run_schedule(SCHEDULE,env)
    sources=[source for i,source in enumerate(base.source_residuals()) if i!=18]
    u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[14]*(u*u-SYM['y_aux']**2);records=[]
    for i,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if i==15 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,i
        records.append(dict(index=i,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=base.bridge.verify_primitives(SCHEDULE,env)
    assert len(primitives)==80 and counts=={'+':36,'*':44}
    assert len(NAMES)==len(set(NAMES))==32 and len(sources)==len(EQUALITIES)==20
    assert all(sp.Symbol('phi') not in source.free_symbols for source in sources)
    return dict(operations=80,multiplications=44,additions_subtractions=36,
                positive_existential_unknown_count=32,equations=20,positive_unknowns=NAMES,
                primitive_instructions=primitives,sources=records,
                deleted_instruction='pell_gap=kappa+phi',deleted_equation='c=pell_gap',
                complete_raw_input_universal_certificate=False,
                deletion_semantic_status='Unresolved; wrong Pell indices alone do not show wrong endpoint powers or raw inputs')


def brute_order(H):
    value=2%H;T=1
    while value!=1:value=value*2%H;T+=1
    assert pow(2,T,H)==1
    return T


def verify_projection():
    cosets=powerpairs=0
    for a in range(2,90):
        M,H=a+1,4*a+3;T=brute_order(H);g=gcd(M,T)
        for u in range(1,min(M,8)):
            residues={pow(2,u+j*M,H) for j in range(T//g)}
            for W in range(1,min(H,70)):
                direct=any(pow(2,v,H)==W for v in range(u,lcm(M,T)+u,M))
                assert direct==(W in residues);cosets+=1
            for w in range(1,20):
                direct=pow(2,w,H) in residues
                assert direct==((w-u)%g==0);powerpairs+=1
    return dict(exact_small_residue_projection_cases=cosets,CRT_power_pair_cases=powerpairs)


def verify_positive_aliases():
    records=[]
    for a in (64,90,128,256,512):
        A=a+2;M=a+1;H=4*a+3;T=brute_order(H);period=lcm(M,T)
        u=4;W=2**u;q=17;J0=23
        assert u<q<J0<M and W<q<A<H
        c=base.bridge.variable.pell(A,J0)[1]
        # Keep the correct endpoint, but force the new index above the main one.
        v=u+period
        mu,kappa=base.bridge.variable.pell(A,v)
        delta,rem=divmod(kappa-u,M);assert rem==0
        rho,rem=divmod(mu-a*kappa-W,H);assert rem==0
        assert min(delta,rho)>0 and kappa>c and v>J0
        assert mu*mu-((a+2)**2-1)*kappa*kappa==1
        records.append(dict(a=a,M=M,H=H,order=T,order_gcd=gcd(M,T),u=u,
                            main_index=J0,alias_index=v,kappa_bits=kappa.bit_length(),
                            correct_endpoint_kept=True,positive_delta_and_rho=True,kappa_exceeds_c=True))
    # A wrong endpoint is possible at a general parameter satisfying the direct
    # index/endpoint bounds and 2**u<A. This is NOT a packed-kernel parameter;
    # in particular it does not satisfy the actual main growth bound 2**q<a.
    a=1024;A=a+2;M=a+1;H=4*a+3;T=brute_order(H)
    u,w,q,J0=4,8,512,600;W=2**w
    assert u<q<J0<M and W<q<A<H and 2**u<A
    # CRT construct v=u modM and v=w modT, then increase past J0.
    assert gcd(M,T)==1
    j=((w-u)*pow(M,-1,T))%T;v=u+M*j
    while v<=J0:v+=M*T
    # Check the norm/index/power congruences by modular Pell powering, avoiding
    # an unnecessary tens-of-millions-bit illustrative norm tuple.
    def pell_mod(index,modulus):
        D=A*A-1
        def mul(p,q):return ((p[0]*q[0]+D*p[1]*q[1])%modulus,
                            (p[0]*q[1]+p[1]*q[0])%modulus)
        value=(1,0);factor=(A%modulus,1)
        while index:
            if index&1:value=mul(value,factor)
            index//=2
            if index:factor=mul(factor,factor)
        return value
    muM,kM=pell_mod(v,M);muH,kH=pell_mod(v,H)
    assert kM==u and (muH-a*kH-W)%H==0 and W!=2**u
    return dict(correct_endpoint_wrong_index_cases=records,
                general_parameter_wrong_endpoint=dict(a=a,q=q,u=u,endpoint_exponent=w,W=W,
                                                       main_index=J0,alias_index=v,
                                                       order=T,order_gcd=1,
                                                       full_main_kernel_growth_bounds=False,
                                                       actual_packed_kernel_parameter=False),
                full_packed_kernel_tuples_materialized=False)


def verify_canonical_small_parameters():
    records=[]
    for r in (1,3):
        X=2**(2*r+1)
        Y=sum(comb(2*r,j)*X**(r-j) for j in range(r+1))
        a=Y*(X+1);M=a+1;H=4*a+3
        factors=sp.factorint(H);T=int(sp.n_order(2,H));g=gcd(M,T)
        assert pow(2,T,H)==1
        for prime in sp.factorint(T):assert pow(2,T//prime,H)!=1
        if r==1:assert g==1
        if r==3:assert g==5
        records.append(dict(r=r,X=X,Y=Y,a=a,M=M,H=H,order=T,order_gcd=g,
                            H_factors={str(p):int(e) for p,e in factors.items()},
                            order_factors={str(p):int(e) for p,e in sp.factorint(T).items()}))
    return dict(cases=records,
                scope='Exact special a=Y(X+1), but r=1 and r=3 are outside the full native compiler geometry; no full false input follows')


def verify():
    return dict(status='PASS_INPUT_PELL_GAP_PROJECTION',source=verify_source(),
                projection=verify_projection(),positive_aliases=verify_positive_aliases(),
                canonical_small_parameters=verify_canonical_small_parameters(),
                proof='../1980/EXPLORATION_INPUT_PELL_GAP_PROJECTION.md',
                complete_universal_improvement=False,complete_universal_deletion_refutation=False,
                scope='Exact gap-deletion projection and full-witness nonredundancy; false raw input at an actual fixed compiler remains unresolved')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['projection']['CRT_power_pair_cases'],'CRT cases; universal deletion unresolved')
