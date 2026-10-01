#!/usr/bin/env python3
"""Complete positive binary-to-radix4 recoding with weaker raw geometry.

This changes the represented function from the radix16 parent. It does
not use the parent's B>=8q^2 transport or claim identical polynomials.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import native_binary_input_dilation130 as parent

geometry=parent.parent.geometry
masked=parent.parent.masked
execute=parent.execute


def build():
    old=parent.build();rows={n:(n,op,a,b) for n,op,a,b in old['source']}
    assert rows['q2']==('q2','*','q','q')
    assert rows['Q']==('Q','*','q2','q2') and rows['B']==('B','*',8,'Q')
    assert {n for n,_,a,b in old['source'] if 'q2' in (a,b)}=={'Q'}
    changed={'Q':('Q','*','q','q'),'B':('B','+','Q','Q')}
    source=[changed.get(n,(n,op,a,b)) for n,op,a,b in old['source'] if n!='q2']
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':65,'A':64} and len(source)==129
    assert len(old['comparisons'])==34 and len(old['auxiliaries'])==49
    return dict(old,source=source,operations=129,multiplications=65,additions_subtractions=64,
                dilation_bit_width=2,changed_geometry_definitions=['Q=q*q','B=Q+Q'],
                removed_geometry_register='q2')


def independent(values):
    q,P,J,K,Ahat,z=(values[n] for n in ('q','P','J','K','Ahat','z'))
    Q=q*q;B=2*Q
    answer=[(B-1)*J+1-P,(2*B-1)*K+1-q*P,values['x']+values['input_slack']-q,
            Ahat+Q-(Q-1)*values['quotient_hat']-z-2,z+values['output_slack']-Q]
    geo=geometry.build(shared_B=True)
    gv={n:values['geo__'+n] for n in geo['auxiliaries']};gv.update(q=q,J=J)
    answer+=geometry.manual(gv,B)
    ms,mp,_=masked.source('and64_prescribed');_,aux=masked.domains('and64_prescribed')
    mv={n:values['and__'+n] for n in aux}
    mv.update(P=q*P,Hhat=values['x']*J+1,Mhat=K+1,Zhat=Ahat)
    env=masked.parent.execute(ms,mv)
    answer += [env[a]-env[b] for a,b in mp]
    return answer


def residuals(packet,values):
    env=execute(packet['source'],values)
    return [env[a]-env[b] for a,b in packet['comparisons']]


def source_checks():
    packet=build();sos,out=parent.parent.sos_source(packet)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
    assert len(sos)==230 and counts=={'M':99,'A':131}
    rng=random.Random(129449)
    for case in range(1024):
        positive=case<640
        values={n:rng.randrange(1,16) if positive else rng.randrange(-7,9)
                for n in packet['parameters']+packet['auxiliaries']}
        env=execute(sos,values);expected=independent(values)
        assert residuals(packet,values)==expected and env[out]==sum(v*v for v in expected)
        if positive:
            assert values['x']*values['J']+1>0 and values['K']+1>0
            assert env['and__padded_A']==16*values['x']*values['J']+12
            assert env['and__padded_B']==16*values['K']+10
    degrees={n:1 for n in packet['parameters']+packet['auxiliaries']}
    for n,op,a,b in packet['source']:
        da=degrees[a] if isinstance(a,str) else 0
        db=degrees[b] if isinstance(b,str) else 0
        degrees[n]=da+db if op=='*' else max(da,db)
    assert max(max(degrees[a],degrees[b]) for a,b in packet['comparisons'])==20
    T=sp.Symbol('T');weights={n:1+i%3 for i,n in enumerate(packet['parameters']+packet['auxiliaries'])}
    values={n:sp.Poly(weights[n]*T+i+1,T) for i,n in enumerate(weights)}
    env=execute(packet['source'],values)
    polys=[env[a]-env[b] for a,b in packet['comparisons']]
    assert max(p.degree() for p in polys)==20
    top=sum(p.LC()**2 for p in polys if p.degree()==20)
    expected=weights['and__w']**4*weights['and__s']**8*weights['and__k']**4*(16*weights['q']*weights['P'])**12
    assert top==expected
    return dict(packet,arbitrary_residual_and_SOS_cases=dict(positive=640,signed=384),
                polynomial=dict(operations=230,multiplications=99,additions_subtractions=131,
                                exact_degree=40,weighted_leading_coefficient=str(top)),
                parent_function_is_different=True)


def spread(x):
    answer=0;j=0
    while x:
        answer+=(x&1)<<(2*j);x>>=1;j+=1
    return answer


def outer_fixture(x,n):
    q=1<<n;assert n>=2 and 0<x<q
    Q=q*q;B=2*Q;P=B**n;J=(P-1)//(B-1);K=(q*P-1)//(2*B-1)
    A=(x*J)&K;z=spread(x)
    assert J>B>=8 and J>q and J&1 and J.bit_count()==n
    assert A==sum(((x>>j)&1)<<(2*(n+1)*j) for j in range(n))
    assert A%(Q-1)==z and 0<z<=(Q-1)//3<Q-1
    assert A>=z and (A-z)%(Q-1)==0
    v=dict(x=x,z=z,q=q,P=P,J=J,K=K,Ahat=A+1,
           quotient_hat=(A-z)//(Q-1)+1,input_slack=q-x,output_slack=Q-z)
    assert all(value>0 for value in v.values())
    assert [(B-1)*J+1-P,(2*B-1)*K+1-q*P,x+v['input_slack']-q,
            A+1+Q-(Q-1)*v['quotient_hat']-z-2,z+v['output_slack']-Q]==[0]*5
    H,M,scale=x*J,K,q*P
    assert 0<H<scale and 0<M<scale
    fields=[16*(scale-1-(H|M))+1,16*(H-A)+4,16*(M-A)+2,16*A+8]
    assert all(f>0 for f in fields) and sum(fields)+1==16*scale
    assert fields[1]+fields[3]==16*H+12 and fields[2]+fields[3]==16*M+10
    return v


def outer_checks():
    cases=ones=zero_quotient=0
    for n in range(2,11):
        for x in range(1,1<<n):
            v=outer_fixture(x,n);cases+=1;ones+=x==(1<<n)-1;zero_quotient+=v['quotient_hat']==1
    rng=random.Random(1294120);packet=build()
    for case in range(512):
        n=rng.randrange(2,121);x=rng.randrange(1,1<<n);v=outer_fixture(x,n);cases+=1
        assert outer_fixture(x,n+1)['z']==v['z']
        if case<128:
            supplied={name:1 for name in packet['parameters']+packet['auxiliaries']};supplied.update(v)
            assert residuals(packet,supplied)[:5]==[0]*5
            assert residuals(packet,supplied)==independent(supplied)
    for x in range(1,4097):
        bits=bin(x)[3:];coded=''.join('01' if b=='1' else '00' for b in bits)
        assert spread(x)==int('1'+coded,2)
        assert spread(spread(x))==parent.parent.spread(x)
    assert spread(3)==5!=3**2
    return dict(genuine_outer_cases=cases,all_ones_cases=ones,zero_unshifted_quotient_cases=zero_quotient,
                padding_invariance_cases=512,raw_outer_source_substitutions=128,
                independent_string_coding_cases=4096,composition_to_radix16_cases=4096,
                smallest_geometry={n:str(v) for n,v in outer_fixture(3,2).items()},
                full_Pell_zeros_materialized=False)


def synchronization_checks():
    candidates=matches=0
    for n in range(1,10):
        q=1<<n;B=2*q*q
        for ell in range(1,513):
            P=1<<ell;candidates+=1
            if (P-1)%(B-1):continue
            J=(P-1)//(B-1)
            accepted=J>B and J>=9 and J>q and J&1 and q==2**J.bit_count()
            expected=n>=2 and ell==(2*n+1)*n
            assert bool(accepted)==expected;matches+=bool(accepted)
    return dict(candidates=candidates,matched_geometries=matches)


def weaker_bootstrap_checks():
    count=0
    for q in range(2,34):
        B=2*q*q
        for gap in range(1,17):
            r=B+gap;X=q*(r//q+1)
            for odd_half in range(1,5):
                Y=q*(2*odd_half+1);E=X*Y;a=Y*(X+1);A=a+2;D=A*A-1;P0=2*X*Y*Y+1
                assert r>=9 and r>q and X>r and Y>=3
                assert E>r+1 and a>2*r+1 and P0>A and 6*X*Y*Y>a
                assert A**10>A*D*D and 6*(r+1)>2*(2*r+1)
                count+=1
    # A genuine smallest geometry lies outside the older B>=8q^2 theorem.
    r,q,B=33,4,32;X=1<<(2*r+1)
    numerator=(X+1)**(2*r);denominator=X**r;Y=numerator//denominator
    a=Y*(X+1);A=a+2;P0=2*X*Y*Y+1
    d,c=geometry.pell(A,2*r+1);chi,k=geometry.pell(P0,r+1)
    v=dict(q=q,J=r,a=a,c=c,d=d,k=k,w=X//q,s=Y//q,
           tau=(chi-1)//2,eta=c-k*Y,zeta=k-(c-k*Y),
           h=(k-r-1)//(X*Y),ga=(d-X-a*c)//(4*a+3),
           odd_half=(Y//q-1)//2,bound_beta=X-r,index_beta=r-B,
           f=1,i=1,j=1,o=1,y_aux=1)
    assert all(value>0 for value in v.values())
    residual=geometry.manual(v,B)
    tested=[0,1,2,3,4,5,6,10,11,12]
    assert all(residual[i]==0 for i in tested)
    assert r<8*q*q and r-B==1 and r-8*q*q==-95
    assert 0<4*(numerator%denominator)<denominator
    return dict(prepower_bootstrap_cases=count,
                partial_kernel=dict(J=r,q=q,B=B,positive_index_slack=1,
                                    old_index_slack=-95,exact_zero_residual_indices=tested,
                                    unasserted_strong_auxiliary_residual_indices=[7,8,9],
                                    maximum_known_coordinate_bits=max(c.bit_length(),k.bit_length()),
                                    full_kernel_zero=False))


def verify():
    return dict(status='PASS_NATIVE_BINARY_INPUT_DILATION129',certificate=source_checks(),
                weaker_bootstrap=weaker_bootstrap_checks(),outer=outer_checks(),
                synchronization=synchronization_checks(),
                scope='Complete positive graph z=sum bit_j(x)*4^j. Raw geometry uses J>=9 '
                      'and J>q directly, not the radix16 B0 transport. Both kernels, same-exponent '
                      'geometry, masks, quotient and bounds are paid. Full astronomical strong '
                      'Pell auxiliaries are proved parametrically, not materialized in fixtures.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
