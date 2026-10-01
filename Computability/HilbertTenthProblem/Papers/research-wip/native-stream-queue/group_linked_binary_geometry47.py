"""Repunit population links the matrix duration to its height parameter.

Shared-B source:47 operations,13 equations,19 positive auxiliaries.
Standalone source computes B=8q^2 and costs49. P typing and the repunit
equation are explicit composition hypotheses, not part of either count.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import comb
from pathlib import Path
import random

import native_binary_three_row_fifo58 as binary


def build(shared_B=True):
    parameters=['q','B','J'] if shared_B else ['q','J']
    auxiliaries=[n for n in binary.CORE_NAMES if n!='r']+['odd_half','bound_beta','index_beta']
    aliases={'r':'J','n2':'q'}
    source=[] if shared_B else [('geometry_q2','*','q','q'),('B','*',8,'geometry_q2')]
    source += [(name,op,aliases.get(left,left),aliases.get(right,right))
               for name,op,left,right in binary.CORE]
    source += [('geometry_even','*',2,'odd_half'),('geometry_odd','+','geometry_even',1),
               ('geometry_X_bound','+','J','bound_beta'),
               ('geometry_index_bound','+','B','index_beta')]
    comparisons=list(binary.prior.CORE_EQUALITIES)+[
        ('s','geometry_odd'),('geometry_X_bound','wn2'),('geometry_index_bound','J')]
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':26 if shared_B else 28,'A':21}
    assert len(comparisons)==13 and len(auxiliaries)==19
    return dict(source=source,comparisons=comparisons,parameters=parameters,auxiliaries=auxiliaries,
                operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
                shared_B=shared_B)


def execute(source,values):
    env=dict(values)
    for name,op,left,right in source:
        assert name not in env
        left=env[left] if isinstance(left,str) else left
        right=env[right] if isinstance(right,str) else right
        env[name]=left*right if op=='*' else left+right if op=='+' else left-right
    return env


def manual(values,B):
    q=values['q'];r=values['J']
    a,c,d,f,h,i,j,k,o,s,w,tau,eta,zeta,ga,y=(values[n] for n in binary.CORE_NAMES if n!='r')
    X=w*q;Y=s*q;E=X*Y;delta=a*a+4*a+3;u=j*c-(2*r+1)
    return [((E*E+X)*(Y*k)**2-tau*(tau+1)),c-Y*k-eta,k-eta-zeta,
            k-r-1-h*E,a-Y*(X+1),d-X-a*c-ga*(4*a+3),
            d*d-1-delta*c*c,(i*c*c)**2-delta*(f*f-1),
            (i*c*c)**2*(u*u-y*y)-(1-y*y),u+c-o*f,
            s-2*values['odd_half']-1,r+values['bound_beta']-X,
            B+values['index_beta']-r]


def source_checks():
    rng=random.Random(4713);records=[]
    for shared in (True,False):
        packet=build(shared)
        for _ in range(512):
            z={n:rng.randrange(1,32) for n in packet['parameters']+packet['auxiliaries']}
            env=execute(packet['source'],z)
            residuals=[env[l]-env[r] for l,r in packet['comparisons']]
            assert residuals==manual(z,env['B'])
        records.append(dict(packet,full_arbitrary_positive_residual_cases=512,
                            positive_auxiliary_count=19,equation_count=13))
    return records


def pell(A,n):
    if n==0:return 1,0
    chi0,chi1=1,A;psi0,psi1=0,1
    for _ in range(1,n):
        chi0,chi1=chi1,2*A*chi1-chi0
        psi0,psi1=psi1,2*A*psi1-psi0
    return chi1,psi1


def bootstrap_checks():
    cases=0
    for q in range(1,17):
        B=8*q*q
        for gap in range(1,13):
            r=B+gap
            for odd_half in range(1,5):
                X=q*(r//q+1);Y=q*(2*odd_half+1)
                E=X*Y;a=Y*(X+1);A=a+2;T=X*Y*Y;P=2*T+1
                assert r>=9 and r>q and X>r and Y>=3
                assert E>r+1 and a>2*r+1 and P>A
                assert 6*T>a and 6*(r+1)>2*(2*r+1)
                # For the unknown p>=r+2>=11, this is a sufficient rank bound.
                assert A**10>A*(A*A-1)**2
                cases+=1
    for r in range(9,129):
        assert 8*r < (r+1)**(r+1)
        assert 2*4**r < (r+1)**(r+1)
        assert 32*r < 2**(2*r+1)+1
    return dict(prepower_fixtures=cases,q_including_one=True,r_lower_bound=9,
                role='Finite checks of elementary estimates; the note proves their uniform bounds.')


def ratio_checks():
    records=[]
    for r in (9,11,13,15,17,19,21,23,25,27,29,31):
        X=2**(2*r+1)
        numerator=(X+1)**(2*r);denominator=X**r
        Y=numerator//denominator;a=Y*(X+1);A=a+2;P=2*X*Y*Y+1
        d,c=pell(A,2*r+1);chi,k=pell(P,r+1)
        difference=c*denominator-k*numerator
        assert difference>0
        assert difference*(X+1)<16*r*k*denominator
        assert Y*k<c<(Y+1)*k
        assert 0<4*(numerator%denominator)<denominator
        q=2**r.bit_count()
        assert X%q==Y%q==0 and (Y//q)%2==1 and Y//q>1
        assert (chi-1)%2==0 and (k-r-1)%(X*Y)==0 and k>r+1
        assert (d-X-a*c)%(4*a+3)==0 and d-X-a*c>0
        assert Y==comb(2*r,r)+sum(comb(2*r,r+j)*X**j for j in range(1,r+1))
        records.append(dict(r=r,q=q,ratio_interval=True,positive_partial_kernel=True,
                            largest_partial_coordinate_bits=max(c.bit_length(),k.bit_length())))
    return dict(fixtures=records,
                scope='Ratio and positive partial-kernel prototypes only. They need not satisfy J>8q^2; full astronomical auxiliary Pell coordinates are supplied by the proof.')


def linked_geometry_checks():
    genuine=0
    for t in range(2,129):
        q=2**t;B=8*q*q;P=B**t;J=(P-1)//(B-1)
        assert J>B and J&1 and J.bit_count()==t
        assert q==2**J.bit_count() and (B-1)*J+1==P
        genuine+=1
    candidates=matches=0
    for q in range(1,65):
        B=8*q*q
        for ell in range(1,513):
            P=2**ell
            if (P-1)%(B-1):continue
            J=(P-1)//(B-1)
            admitted=J>B and J&1 and q==2**J.bit_count()
            expected=False
            if q&(q-1)==0:
                t=q.bit_length()-1
                expected=t>=2 and ell==(3+2*t)*t
            assert bool(admitted)==expected
            candidates+=1;matches+=bool(admitted)
    return dict(actual_durations_2_through128=genuine,dyadic_P_divisibility_candidates=candidates,
                matched_exact_linked_geometries=matches,
                external_composition_relations='P dyadic; (B-1)J+1=P; B=8q^2.')


def verify():
    return dict(status='PASS_GROUP_LINKED_BINARY_GEOMETRY47',source=source_checks(),
                bootstrap=bootstrap_checks(),ratio=ratio_checks(),linked=linked_geometry_checks(),
                core_sha256=hashlib.sha256(json.dumps(binary.CORE,separators=(',',':')).encode()).hexdigest(),
                exact_shared_projection='Under B=8q^2: J>B, J odd, q=2^popcount(J).',
                exact_linked_projection='Together with P dyadic and (B-1)J+1=P: q=2^t, B=8q^2, P=B^t, t>=2.',
                limit='Neither P power typing nor the repunit equation is included in47/49. Native scale q is the matrix height parameter here, not a selector-kernel scale from another component.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
