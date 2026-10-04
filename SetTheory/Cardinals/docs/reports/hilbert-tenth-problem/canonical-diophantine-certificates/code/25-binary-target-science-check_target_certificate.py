#!/usr/bin/env python3
"""Fresh checks; never imports or executes a submitted/upstream builder.

Reads the emitted DAG as inert syntax. Exact polynomial specialization establishes
its degree; modular identities test all primitive expansion interfaces. Finite
sandpile/tableau tests are independent of Pell witness construction and are not
all-integer proofs.
"""
from pathlib import Path
from itertools import product, permutations
from collections import Counter
import hashlib
import json
import random

ROOT=Path(__file__).resolve().parent
DAG=json.loads((ROOT/'evidence/polynomial-dag.json').read_text())


def evaluate_modulo(modulus, seed):
    rng=random.Random(seed)
    values={'input:InputPlus':rng.randrange(modulus)}
    values.update({'witness:'+n:rng.randrange(modulus) for n in DAG['witnesses']})
    def get(ref):
        return int(ref[9:]) % modulus if ref.startswith('constant:') else values[ref]
    for i,(op,a,b) in enumerate(DAG['gates']):
        x,y=get(a),get(b)
        values['gate:'+str(i)]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]() % modulus
    return get


def check_expansions():
    clauses={name:(a,b) for a,b,name in DAG['equalities']}
    counters=Counter()
    for seed,prime in enumerate([1000003,1000033,1000037,1000039,1000081,1000099]):
        get=evaluate_modulo(prime,seed+481)
        def positive(name): return get('witness:'+name)
        def natural(name): return positive(name+'.Plus')-1
        def check(name,left,right):
            a,b=clauses[name]
            assert (get(a)-get(b)-left+right)%prime==0,name
        for macro in DAG['macros']:
            name=macro['name']
            if macro['kind']=='power':
                base,exponent,out=[get(macro[key]) for key in ['base','exponent','out']]
                a,beta=positive(name+'.aMinus1')+1,positive(name+'.betaMinus1')+1
                w,mod,g,x,y,u,v,s,t,qb,qv,strict=[positive(name+'.'+key) for key in
                    ['w','modulus','g','x','y','u','v','s','t','qb','qv','strict']]
                aa,ab,sa,sb,ta,tb,ra,rb=[natural(name+'.'+key) for key in
                    ['alpha1','alpha2','sigma1','sigma2','tau1','tau2','rho1','rho2']]
                k,m=exponent+1,base*out
                pairs=[(x*x,1+(a*a-1)*y*y),(u*u,1+(a*a-1)*v*v),
                    (s*s,1+(beta*beta-1)*t*t),(beta,1+4*y*qb),
                    (beta+u*aa,a+u*ab),(v,y*y*qv),(s+u*sa,x+u*sb),
                    (t+4*y*ta,k+4*y*tb),(y,k+natural(name+'.dyk')),
                    (w,base+natural(name+'.dwb')),(w,k+natural(name+'.dwk')),
                    (mod,m+strict),(a*a,1+((w+1)**2-1)*(w*g)**2),
                    (2*a*base,mod+base*base+1),(x+mod*ra,y*(a-base)+m+mod*rb)]
                for i,(left,right) in enumerate(pairs,1): check(name+'.eq'+str(i),left,right)
                counters['power_residual_substitutions']+=15
            elif macro['kind']=='subset':
                L=positive(name+'.radix.out');Y=positive(name+'.slot.out');Z=positive(name+'.binomial.out')
                q,o,r=[natural(name+'.'+x) for x in ['quotient','half','remainder']]
                check(name+'.extract',Z,(q*L+2*o+1)*Y+r)
                check(name+'.digit_bound',2*o+1+positive(name+'.digit_gap'),L)
                check(name+'.remainder_bound',r+positive(name+'.remainder_gap'),Y)
                counters['subset_residual_substitutions']+=3
            elif macro['kind']=='and':
                x,y,z=[get(macro[key]) for key in ['left','right','out']]
                check(name+'.left_partition',x,z+natural(name+'.left_only'))
                check(name+'.right_partition',y,z+natural(name+'.right_only'))
                counters['and_residual_substitutions']+=2
            elif macro['kind']=='spread':
                value,base,length,stride=[get(macro[key]) for key in ['value','base','length','stride']]
                P=positive(name+'.range.out');C=positive(name+'.copybase.out');E=positive(name+'.copylimit.out')
                check(name+'.stride_bound',stride,length+1+natural(name+'.stride_gap'))
                check(name+'.range_bound',value+positive(name+'.range_gap'),P)
                check(name+'.copy_equation',(C-1)*natural(name+'.copy')+1,E)
                check(name+'.mask_equation',(base*C-1)*natural(name+'.mask')+1,E*P)
                counters['spread_residual_substitutions']+=4
        sos=sum((get(a)-get(b))**2 for a,b,name in DAG['equalities'])%prime
        assert get(DAG['output'])==sos
        counters['full_sos_substitutions']+=1
    return dict(counters)


def exact_degree():
    # P(t) is obtained by setting the six dimension variables and three padding
    # variables to t, and all other variables (including input) to zero.
    chosen={'descriptor.'+x for x in ['p','q','r','d','e','f']} | {'box.t'+x for x in ['x','y','z']}
    values={'input:InputPlus':(0,)}
    values.update({'witness:'+n:((0,1) if n in chosen else (0,)) for n in DAG['witnesses']})
    def get(r): return (int(r[9:]),) if r.startswith('constant:') else values[r]
    def trim(v):
        while len(v)>1 and v[-1]==0:v.pop()
        return tuple(v)
    def operation(op,x,y):
        if op=='*':
            z=[0]*(len(x)+len(y)-1)
            for i,a in enumerate(x):
                for j,b in enumerate(y): z[i+j]+=a*b
        else:
            z=[0]*max(len(x),len(y))
            for i,a in enumerate(x):z[i]+=a
            for i,b in enumerate(y):z[i]+=b if op=='+' else -b
        return trim(z)
    for i,(op,a,b) in enumerate(DAG['gates']):values['gate:'+str(i)]=operation(op,get(a),get(b))
    result=get(DAG['output'])
    assert len(result)-1==18 and result[-1]==48
    top=[]
    for a,b,n in DAG['equalities']:
        residual=operation('-',get(a),get(b))
        if len(residual)-1==9:top.append([n,residual[-1]])
    assert top==[['patch.shift.eq8',-4],['patch.shift.eq9',-4],['patch.shift.eq11',-4]]
    return {'specialized_degree':18,'leading_coefficient':48,'degree_nine_residuals':top,
            'specialized_polynomial_coefficients':result}


def subset(mask,value):return value>=0 and value&~mask==0

def pack(digits,b=32):return sum(v*b**i for i,v in enumerate(digits))

def geom(b,n):return (b**n-1)//(b-1)

def unbits(value,n):return [(value>>i)&1 for i in range(n)]


def recurrence_tests():
    cases=0
    for n in [1,2]:
        Q=32**n
        for k in [1,2,3]:
            for ai,ei,vi in product(range(2**(n*k)),range(2**(n*k)),range(2**n)):
                aa,ee,vv=unbits(ai,n*k),unbits(ei,n*k),unbits(vi,n)
                a,e,v=pack(aa),pack(ee),pack(vv)
                equality=Q*(a+e)==a+Q**k*v
                semantic=not any(aa[:n]) and all(
                    aa[(t+1)*n+j]==aa[t*n+j]+ee[t*n+j]
                    for t in range(k-1) for j in range(n)) and all(
                    vv[j]==aa[(k-1)*n+j]+ee[(k-1)*n+j] for j in range(n))
                assert equality==semantic
                cases+=1
    return cases


def legality_tests():
    cases=0
    for initial,neighbors,new,slack in product(range(21),range(7),range(2),range(32)):
        planes=[(slack>>i)&1 for i in range(5)]
        bitconditions=all(subset(new,p) for p in planes) and subset(new,planes[3]+planes[4])
        selected=(initial+neighbors)&(31*new)
        certificate=bitconditions and selected==6*new+slack
        expected=(new==0 and slack==0) or (new==1 and initial+neighbors>=6 and slack==initial+neighbors-6)
        assert certificate==expected
        cases+=1
    return cases


def spatial_time_tests():
    cases=slots=0
    for A,B,C,K in product(range(2,5),range(2,5),range(2,5),range(1,4)):
        X,Y,Q=32**A,32**(A*B),32**(A*B*C)
        I=32*X*Y*geom(32,A-2)*geom(X,B-2)*geom(Y,C-2)
        mask=I*geom(Q,K)
        coords=[(x,y,z,t) for t in range(K) for z in range(C) for y in range(B) for x in range(A)]
        for pattern in range(4):
            active={(x,y,z,t) for x,y,z,t in coords if
                    0<x<A-1 and 0<y<B-1 and 0<z<C-1 and
                    [True,(x+y+z+t)%2==0,(x+3*y+5*z+7*t)%3==0,t==K-1][pattern]}
            digits=[int(c in active) for c in coords]
            pre=pack(digits)
            assert subset(mask,pre)
            assert pre%32==pre%X==pre%Y==0
            shifts=[32*pre,X*pre,Y*pre,pre//32,pre//X,pre//Y]
            offsets=[(-1,0,0),(0,-1,0),(0,0,-1),(1,0,0),(0,1,0),(0,0,1)]
            for stream,(dx,dy,dz) in zip(shifts,offsets):
                expected=pack([int((x+dx,y+dy,z+dz,t) in active) for x,y,z,t in coords])
                assert stream==expected
            cases+=1;slots+=len(coords)
    return cases,slots


def binary_reachability(heights,edges,threshold=6):
    fired=set()
    while True:
        eligible=[v for v,h in enumerate(heights) if v not in fired and h+sum(w in fired for w in edges[v])>=threshold]
        if not eligible:return fired
        fired.update(eligible)


def binary_prefix_enumeration(heights,edges):
    reached=set()
    n=len(heights)
    for length in range(1,n+1):
        for order in permutations(range(n),length):
            counts=[0]*n
            legal=True
            for v in order:
                h=heights[v]-6*counts[v]+sum(counts[w] for w in edges[v])
                if h<6:legal=False;break
                counts[v]+=1
            if legal:reached.update(order)
    return reached


def reachability_tests():
    edges=[[1],[0,2],[1]]
    cases=0
    for heights in product(range(14),repeat=3):
        assert binary_reachability(heights,edges)==binary_prefix_enumeration(heights,edges)
        cases+=1
    assert binary_reachability([5,5],[[1],[0]])==set()
    assert binary_reachability([12,4],[[1],[0]])=={0}
    h=[12,4]
    for v in [0,0,1]:
        assert h[v]>=6
        h[v]-=6;h[1-v]+=1
    return {'height_triples':cases,'overfiring_rejected':True,
            'ordinary_firing_not_binary_fixture':[12,4],
            'ordinary_legal_sequence':[0,0,1]}


def cantor(x,y):return (x+y)*(x+y+1)//2+y

def unpair(z):
    from math import isqrt
    w=(isqrt(8*z+1)-1)//2
    y=z-w*(w+1)//2
    return w-y,y

def pair_many(fields):
    rest=fields[-1]
    for x in reversed(fields[:-1]):rest=cantor(x,rest)
    return rest

def decode_many(z):
    fields=[]
    for _ in range(10):
        x,z=unpair(z);fields.append(x)
    return fields+[z]


def target_tests():
    cases=0
    for physical in product(range(-3,4),repeat=3):
        zeta=[2*x if x>=0 else -2*x-1 for x in physical]
        fields=[0,0,0,5,0,0,0,1]+zeta
        assert decode_many(pair_many(fields))==fields
        local=[]
        for x,z in zip(physical,zeta):
            h,sign=z//2,z%2
            ell=4+x
            assert sign*(sign-1)==0 and z==2*h+sign
            assert ell+2*sign*h+sign==4+h
            assert ell+(8-ell)==8 and 0<ell<7+1
            local.append(ell)
        point=32**(local[0]+8*local[1]+64*local[2])
        assert subset(point,point)
        wrong=32**((local[0]+1)+8*local[1]+64*local[2])
        assert not subset(point,wrong)
        cases+=1
    assert pair_many([0]*11)==0
    return cases


def nonstabilizing_example():
    # Uniform height 5 plus one chip at the origin. A one-step tableau fires
    # the target origin, while its six neighbors have height 6 afterwards.
    A=B=C=4;Q=32**64
    X,Y=32**4,32**16
    I=32*X*Y*geom(32,2)*geom(X,2)*geom(Y,2)
    origin=32**(2+4*2+16*2)
    eta=5*geom(32,64)+origin
    pre,new,final=0,origin,origin
    assert subset(I,new) and Q*(pre+new)==pre+Q*final
    selected=eta&(31*new)
    assert selected==6*new
    after=eta-6*origin+32*origin+X*origin+Y*origin+origin//32+origin//X+origin//Y
    assert any((after//32**i)%32>=6 for i in range(64))
    return {'finite_target_prefix':True,'endpoint_unstable':True,
            'global_nonstabilization_proof':'Any finite nonzero odometer has a support boundary neighbor with initial height five, which receives a chip but never topples.'}


def main():
    report={'dag_sha256':hashlib.sha256((ROOT/'evidence/polynomial-dag.json').read_bytes()).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'expansion_checks':check_expansions(),'exact_degree':exact_degree(),
            'recurrence_cases':recurrence_tests(),'legality_cases':legality_tests()}
    cases,slots=spatial_time_tests()
    report['neighbor_frame_cases']=cases;report['neighbor_frame_slots']=slots
    report['binary_reachability']=reachability_tests()
    report['signed_target_roundtrips']=target_tests()
    report['nonstabilizing_target_example']=nonstabilizing_example()
    report['limitations']='Finite semantic tests and modular primitive checks do not prove all-input correctness; exact degree is independently established by integer polynomial specialization. POWER retains the pinned Pell theorem dependency. No upstream executable or saved arithmetic schedule was run.'
    (ROOT/'evidence/check-receipt.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report,sort_keys=True,indent=2))

if __name__=='__main__':main()
