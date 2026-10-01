#!/usr/bin/env python3
"""Complete positive binary-to-radix16 recoding with two paid native kernels.

Full Pell witnesses are established parametrically in the note. The finite
tests materialize outer words and audit every literal comparison off zero.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import group_linked_binary_geometry47 as geometry
import native_binary_masked_selection63 as masked


def rename(value,prefix,aliases):
    return aliases.get(value,prefix+value) if isinstance(value,str) else value


def imported(source,pairs,prefix,aliases):
    f=lambda x:rename(x,prefix,aliases)
    return [(f(n),op,f(a),f(b)) for n,op,a,b in source],[(f(a),f(b)) for a,b in pairs]


def build():
    source=[('q2','*','q','q'),('Q','*','q2','q2'),('B','*',8,'Q'),
            ('scale','*','q','P'),('Bm1','-','B',1),('repunit_product','*','Bm1','J'),
            ('repunit_P','+','repunit_product',1),('twiceB','+','B','B'),
            ('twiceBm1','-','twiceB',1),('mask_product','*','twiceBm1','K'),
            ('mask_scale','+','mask_product',1),('copies','*','x','J'),
            ('Hhat','+','copies',1),('Mhat','+','K',1),
            ('input_bound','+','x','input_slack'),('modulus','-','Q',1),
            ('quotient_product','*','modulus','quotient_hat'),
            ('congruence_left','+','Ahat','Q'),('congruence_right0','+','quotient_product','z'),
            ('congruence_right','+','congruence_right0',2),('output_bound','+','z','output_slack')]
    pairs=[('repunit_P','P'),('mask_scale','scale'),('input_bound','q'),
           ('congruence_left','congruence_right'),('output_bound','Q')]
    geo=geometry.build(shared_B=True);ga={'q':'q','B':'B','J':'J'}
    gs,gp=imported(geo['source'],geo['comparisons'],'geo__',ga)
    ms,mp,_=masked.source('and64_prescribed');ma={'P':'scale','Hhat':'Hhat','Mhat':'Mhat','Zhat':'Ahat'}
    als,alp=imported(ms,mp,'and__',ma)
    _,and_aux=masked.domains('and64_prescribed')
    witnesses=['q','P','J','K','Ahat','quotient_hat','input_slack','output_slack']
    witnesses += ['geo__'+v for v in geo['auxiliaries']]+['and__'+v for v in and_aux]
    source+=gs+als;pairs+=gp+alp
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':67,'A':65} and len(source)==132 and len(pairs)==34 and len(witnesses)==49
    return dict(parameters=['x','z'],auxiliaries=witnesses,source=source,comparisons=pairs,
                operations=132,multiplications=67,additions_subtractions=65,
                witnesses=49,equations=34)


def execute(source,values):return geometry.execute(source,values)


def residuals(packet,values):
    env=execute(packet['source'],values)
    return [env[a]-env[b] for a,b in packet['comparisons']]


def independent(values):
    q,P,J,K,Ahat,z=(values[n] for n in ('q','P','J','K','Ahat','z'))
    Q=q**4;B=8*Q
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


def sos_source(packet):
    source=list(packet['source']);last=None
    for i,(a,b) in enumerate(packet['comparisons']):
        r,s=f'residual_{i}',f'square_{i}'
        source.extend(((r,'-',a,b),(s,'*',r,r)))
        if last is None:last=s
        else:
            total=f'sum_{i}';source.append((total,'+',last,s));last=total
    return source,last


def source_checks():
    packet=build();sos,out=sos_source(packet)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
    assert len(sos)==233 and counts=={'M':101,'A':132}
    degrees={n:1 for n in packet['parameters']+packet['auxiliaries']}
    for name,op,a,b in packet['source']:
        da=degrees[a] if isinstance(a,str) else 0
        db=degrees[b] if isinstance(b,str) else 0
        degrees[name]=da+db if op=='*' else max(da,db)
    assert max(max(degrees[a],degrees[b]) for a,b in packet['comparisons'])==20
    rng=random.Random(1321649)
    for case in range(768):
        values={n:rng.randrange(1,13) if case<512 else rng.randrange(-5,7)
                for n in packet['parameters']+packet['auxiliaries']}
        expected=independent(values);env=execute(sos,values)
        assert residuals(packet,values)==expected
        assert env[out]==sum(r*r for r in expected)
        if case<512:
            assert env['B']>=8*values['q']**2 and env['Hhat']>0 and env['Mhat']>0
    T=sp.Symbol('T')
    weights={n:1+i%3 for i,n in enumerate(packet['parameters']+packet['auxiliaries'])}
    values={n:sp.Poly(weights[n]*T+i+1,T) for i,n in enumerate(weights)}
    env=execute(packet['source'],values)
    polys=[env[a]-env[b] for a,b in packet['comparisons']]
    assert max(p.degree() for p in polys)==20
    top=sum(p.LC()**2 for p in polys if p.degree()==20)
    expected_top=weights['and__w']**4*weights['and__s']**8*weights['and__k']**4*(16*weights['q']*weights['P'])**12
    assert top==expected_top>0
    return dict(packet,arbitrary_residual_and_SOS_cases=dict(positive=512,signed=256),
                polynomial=dict(operations=233,multiplications=101,additions_subtractions=132,
                                exact_degree=40,weighted_leading_coefficient=str(top)),
                source_domain='All49 auxiliary coordinates and the two parameters x,z are positive.')


def spread(x):
    value=0;position=0
    while x:
        value+=(x&1)<<(4*position);position+=1;x>>=1
    return value


def outer_fixture(x,n):
    q=1<<n;assert n>=2 and 0<x<q
    Q=q**4;B=8*Q;P=B**n;J=(P-1)//(B-1);K=(q*P-1)//(2*B-1)
    copies=x*J;A=copies&K;z=spread(x)
    assert (B-1)*J+1==P and (2*B-1)*K+1==q*P
    assert J>B and J&1 and J.bit_count()==n and q==2**J.bit_count()
    assert copies<q*P and K<q*P
    assert A==sum(((x>>j)&1)<<(4*(n+1)*j) for j in range(n))
    assert A%(Q-1)==z and 0<z<=(Q-1)//15<Q-1
    assert A>=z and (A-z)%(Q-1)==0
    values=dict(x=x,z=z,q=q,P=P,J=J,K=K,Ahat=A+1,
                quotient_hat=(A-z)//(Q-1)+1,input_slack=q-x,output_slack=Q-z)
    assert all(v>0 for v in values.values())
    assert independent_outer(values)==[0]*5
    # Actual padded Boolean partition. These are not complete Pell fixtures.
    H,M=copies,K;scale=q*P
    fields=[16*(scale-1-(H|M))+1,16*(H-A)+4,16*(M-A)+2,16*A+8]
    assert all(v>0 for v in fields) and sum(fields)+1==16*scale
    assert fields[1]+fields[3]==16*(H+1)-4
    assert fields[2]+fields[3]==16*(M+1)-6
    return values


def independent_outer(v):
    q,P,J,K,Ahat,z=(v[n] for n in ('q','P','J','K','Ahat','z'))
    Q=q**4;B=8*Q
    return [(B-1)*J+1-P,(2*B-1)*K+1-q*P,v['x']+v['input_slack']-q,
            Ahat+Q-(Q-1)*v['quotient_hat']-z-2,z+v['output_slack']-Q]


def outer_checks():
    count=ones=quotient_zero=0
    for n in range(2,11):
        for x in range(1,1<<n):
            v=outer_fixture(x,n);count+=1;ones+=x==(1<<n)-1;quotient_zero+=v['quotient_hat']==1
    rng=random.Random(164132)
    for _ in range(512):
        n=rng.randrange(2,81);x=rng.randrange(1,1<<n);v=outer_fixture(x,n);count+=1
        assert spread(x)==outer_fixture(x,n+1)['z']
    # Spreading is exactly a sentinel-preserving uniform binary code.
    for x in range(1,2049):
        word=bin(x)[3:]
        coded=''.join('0001' if bit=='1' else '0000' for bit in word)
        assert spread(x)==int('1'+coded,2)
        assert spread(spread(x))==sum(((x>>j)&1)<<(16*j) for j in range(x.bit_length()))
    assert spread(3)==17!=3**4
    return dict(genuine_outer_dilation_cases=count,all_ones_boundary_cases=ones,
                zero_unshifted_quotient_cases=quotient_zero,padding_invariance_cases=512,
                independent_string_coding_cases=2048,twice_iterated_width16_cases=2048,
                polynomial_loader_obstruction_witness=dict(x=3,dilation=17,fourth_power=81),
                full_Pell_zeros_materialized=False,
                small_example={n:str(v) for n,v in outer_fixture(5,3).items()})


def synchronization_checks():
    candidates=admitted=0
    for exponent in range(1,9):
        q=1<<exponent;B=8*q**4
        for ell in range(1,513):
            P=1<<ell;candidates+=1
            if (P-1)%(B-1):continue
            J=(P-1)//(B-1)
            actual=J>B and J&1 and q==2**J.bit_count()
            target=exponent>=2 and ell==(4*exponent+3)*exponent
            assert bool(actual)==target
            admitted+=bool(actual)
    return dict(dyadic_repunit_population_candidates=candidates,matched_geometries=admitted,
                scope='Finite synchronization audit; the note proves exact equivalence for all exponents.')


def verify():
    return dict(status='PASS_NATIVE_BINARY_INPUT_DILATION132',certificate=source_checks(),
                outer=outer_checks(),synchronization=synchronization_checks(),
                scope='Complete positive relation z=sum bit_j(x)*16^j, with both native kernels '
                      'and all geometry, mask, congruence and size comparisons paid. Full Pell '
                      'converse is parametric, not a claimed numerical fixture. A PCP program '
                      'interface and universal selected history remain separate obligations.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
