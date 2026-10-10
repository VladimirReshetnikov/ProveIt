#!/usr/bin/env python3
"""Independent raw-matrix Smith checks, requiring SymPy.

No import of the normal-form generator. Matrices are assembled directly
from the defining distribution and reflection relations, including jets.
"""
from itertools import product, combinations
from pathlib import Path
import json
import math
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form
ROOT=Path(__file__).resolve().parents[1]

if not __debug__:
    raise RuntimeError('Run without -O: exact validation uses assertions.')


def primes(q):
    return tuple(p for p in range(2,q+1) if q%p==0 and sp.isprime(p))

def phi(q):
    return sum(math.gcd(a,q)==1 for a in range(q))

def rows(q, weights, L=1, epsilon=None):
    out=[]
    for p in primes(q):
        for k in range(q//p):
            for h in range(L):
                r=[0]*(q*L)
                for j in range(p):r[(k+j*q//p)*L+h]+=1
                for t,c in enumerate(weights[p]):
                    if h+t<L:r[p*k*L+h+t]-=c
                out.append(r)
    if epsilon is not None:
        for a in range(q):
            for h in range(L):
                r=[0]*(q*L)
                r[(-a%q)*L+h]+=1
                r[a*L+h]-=epsilon
                out.append(r)
    return sp.Matrix(out)

def smith_info(M):
    D=smith_normal_form(M,domain=sp.ZZ)
    d=[abs(int(D[j,j])) for j in range(min(D.shape)) if D[j,j]]
    return {'free_rank':M.cols-len(d), 'nonzero_invariants':d,
            'ones':d.count(1), 'twos':d.count(2)}

def binary_product(a,b,L):
    out=0
    for j in range(L):
        if (b>>j)&1:out^=a<<j
    return out&((1<<L)-1)

def expected(q, weights, L):
    r=sum(p!=2 for p in weights)+int(q%4==0)
    if q==2:return (L,0,0,L)
    vv=[]
    for p,c in weights.items():
        a=sum((x%2)<<j for j,x in enumerate(c[:L]))
        f=(a^1) if p!=2 else binary_product(a,a^1,L)
        if p!=2 or q%4==0:
            vv.append(L if f==0 else (f&-f).bit_length()-1)
    h=min(vv)*2**(r-1)
    return (L*phi(q)//2,h,L*phi(q)//2,h)

def main():
    records=[]
    for q in [2,3,4,5,6,8,9,10,12,15,18,20,24,30,36,60]:
        for bits in product([0,1],repeat=len(primes(q))):
            w={p:[b] for p,b in zip(primes(q),bits)}
            full=smith_info(rows(q,w))
            assert full['free_rank']==phi(q) and all(d==1 for d in full['nonzero_invariants'])
            fp,hp,fm,hm=expected(q,w,1)
            for eps,fr,h in [(1,fp,hp),(-1,fm,hm)]:
                si=smith_info(rows(q,w,epsilon=eps))
                assert si['free_rank']==fr and si['twos']==h
                assert all(d in (1,2) for d in si['nonzero_invariants'])
                records.append(dict(q=q,length=1,weights=w,epsilon=eps,**si))
    jet_specs=[(3,2,{3:[1,1]}), (3,4,{3:[1,2,0,1]}), (4,4,{2:[1,1]}),
               (9,5,{3:[1,2,0,1]}), (12,4,{2:[1,1],3:[1,0,0,1]}),
               (15,5,{3:[1,0,1],5:[1,2,0,1]}),
               (30,3,{2:[-2,1],3:[3,2,1],5:[-1,0,1]}),
               (60,3,{2:[2,0,1],3:[1,0,1],5:[1,0,1]})]
    for q,L,w in jet_specs:
        full=smith_info(rows(q,w,L))
        assert full['free_rank']==L*phi(q) and all(d==1 for d in full['nonzero_invariants'])
        fp,hp,fm,hm=expected(q,w,L)
        for eps,fr,h in [(1,fp,hp),(-1,fm,hm)]:
            si=smith_info(rows(q,w,L,eps))
            assert si['free_rank']==fr and si['twos']==h
            assert all(d in (1,2) for d in si['nonzero_invariants'])
            records.append(dict(q=q,length=L,weights=w,epsilon=eps,**si))
    result={'sympy_version':sp.__version__,'reflected_smith_cases':len(records),
            'unreflected_smith_cases':len(records)//2,'all_passed':True,'cases':records}
    (ROOT/'data'/'smith_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
if __name__=='__main__': main()
