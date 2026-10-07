#!/usr/bin/env python3
"""Finite exact cycle-index counts and independent symmetric-margin enumeration.

The cycle-index identities are from Schwob, arXiv:2506.04007v1, Section 4.3.
The independent margin recursion counts labelled row positions, even when their
margins agree. This code does not quotient by simultaneous permutations.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, comb
from common import emit, integer, require, new_file_path

MAX_N = 20
MAX_MONOMIALS = 3000
A = (1,1,3,7,21,57,182,565,1931,6670,24537,92337,364602,
     1477148,6219031,26875932,119930947,548688443,2580814003,
     12425175838,61302331782)
B = (1,1,5,19,107,573,4050,29093,249301,2271020,23378901,257871081,
     3132494380,40693204728,572089068459,8566311524788,137165829681775,
     2327192535461323,41865158805428687,793982154675640340,15863206077534914434)
C = (1,1,4,15,82,457,3231,24055,209375,1955288,20455936,229830841,
     2828166755,37228913365,528635368980,7990596990430,128909374528433,
     2202090635802581,39837079499488151,759320365206705013,15234890522990662422)

@lru_cache(maxsize=1000)
def _partitions(n, minimum):
    if n == 0:
        return ((),)
    return tuple((k,)+p for k in range(minimum,n+1) for p in _partitions(n-k,k))

def partitions(n, minimum=1):
    integer(n,0,MAX_N,'partition weight')
    integer(minimum,1,MAX_N,'minimum part')
    return _partitions(n, minimum)

def _partition(part):
    require(isinstance(part,(tuple,list)), 'partition must be a tuple or list')
    require(len(part)<=MAX_N, 'partition length cutoff')
    result=tuple(integer(v,1,MAX_N,'part') for v in part)
    require(sum(result)<=MAX_N,'partition weight cutoff')
    return result

def centralizer(part):
    result=1
    for j,m in Counter(_partition(part)).items():
        result*=j**m*factorial(m)
    return result

def square_roots(part):
    result=1
    for j,m in Counter(_partition(part)).items():
        if j%2==0:
            if m%2:
                return 0
            result*=factorial(m)*j**(m//2)//(2**(m//2)*factorial(m//2))
        else:
            result*=sum(factorial(m)*j**k//(factorial(m-2*k)*2**k*factorial(k))
                        for k in range(m//2+1))
    return result

def _multiply(a,b,N):
    result=defaultdict(F)
    for p,v in a.items():
        for q,w in b.items():
            if sum(p)+sum(q)<=N:
                result[tuple(sorted(p+q))]+=v*w
                require(len(result)<=MAX_MONOMIALS,'polynomial monomial budget exceeded')
    return dict(result)

def _reciprocal(d,N):
    result={():F(1)}
    power={():F(1)}
    minimum=min(map(sum,d)) if d else N+1
    for _ in range(N//minimum):
        power=_multiply(power,d,N)
        for p,v in power.items():
            result[p]=result.get(p,F())+v
            require(len(result)<=MAX_MONOMIALS,'polynomial monomial budget exceeded')
    return result

def cycle_index_counts(n=MAX_N):
    integer(n,0,MAX_N,'exact cutoff')
    product={():F(1)}
    for j in range(1,n+1):
        h={p:F(1,centralizer(p)) for p in partitions(j)}
        product=_multiply(product,_reciprocal(h,n),n)
    a=[F() for _ in range(n+1)]
    b=[F() for _ in range(n+1)]
    c=[F() for _ in range(n+1)]
    for p,v in product.items():
        k=sum(p); z=centralizer(p)
        a[k]+=v*square_roots(p)
        b[k]+=v*v*z
        c[k]+=v*v*z*(-1)**(k-len(p))
    require(all(v.denominator==1 for v in a+b+c),'cycle-index count is not integral')
    result=[list(map(int,values)) for values in (a,b,c)]
    require(result==[list(values[:n+1]) for values in (A,B,C)],'reference sequence mismatch')
    return result

def involutions(n):
    integer(n,0,MAX_N,'involution index')
    a,b=1,1
    for k in range(2,n+1):
        a,b=b,b+(k-1)*a
    return b

def _allocations(degree,multiplicity,budget):
    def rec(value,remaining,weight,counts,multiplier):
        if value == 0:
            ds=[]
            for r,c in zip(range(min(degree,budget),-1,-1),counts+[remaining]):
                if degree-r:
                    ds.extend([degree-r]*c)
            yield weight,tuple(ds),multiplier
            return
        for c in range(min(remaining,(budget-weight)//value)+1):
            yield from rec(value-1,remaining-c,weight+c*value,
                           counts+[c],multiplier*comb(remaining,c))
    yield from rec(min(degree,budget),multiplicity,0,[],1)

@lru_cache(maxsize=50000)
def _matrices(margins):
    if not margins:
        return 1
    if margins[-1] == 1:
        return involutions(len(margins))
    d=margins[0]
    groups=list(Counter(margins[1:]).items())
    def rec(i,budget,residual,mult):
        if i==len(groups):
            return mult*_matrices(tuple(sorted(residual)))
        degree,count=groups[i]
        return sum(rec(i+1,budget-used,residual+ds,mult*w)
                   for used,ds,w in _allocations(degree,count,budget))
    return rec(0,d,(),1)

def symmetric_matrices(margins):
    """Count symmetric matrices with these labelled positive row margins."""
    return _matrices(tuple(sorted(_partition(margins))))

def margin_counts(n=MAX_N):
    integer(n,0,MAX_N,'margin cutoff')
    counts=[sum(symmetric_matrices(p) for p in partitions(k)) for k in range(n+1)]
    require(counts==list(A[:n+1]),'independent symmetric-margin count mismatch')
    for k in range(2,n+1):
        require(2*symmetric_matrices((2,)+(1,)*(k-2))==involutions(k),'two-margin identity')
    for k in range(3,n+1):
        require(6*symmetric_matrices((3,)+(1,)*(k-3))==involutions(k)+2*involutions(k-3),'three-margin identity')
    return counts

def verify(n=MAX_N):
    integer(n,0,MAX_N,'exact cutoff')
    a,b,c=cycle_index_counts(n)
    independent=margin_counts(n)
    require(independent==a,'independent method disagreement')
    return {'status':'PASS','N':n,'A104779':a,'A321652':b,
            'A068313_with_empty_extension':c,
            'matched_OEIS_ranges':{'A104779':[0,n],'A321652':[0,n],
                                  'A068313':[1,n] if n else []},
            'independent_symmetric_margin_counts':independent,
            'fixed_margin_identities':'2*M(2,1^(n-2))=I_n; 6*M(3,1^(n-3))=I_n+2*I_(n-3)',
            'arithmetic':'exact integers and fractions.Fraction',
            'source':'https://arxiv.org/html/2506.04007v1#S4.SS3',
            'scope':'Finite identities and counts only; c_0=1 is an empty-object extension, not an OEIS offset claim.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n',type=int,default=MAX_N)
    parser.add_argument('--output')
    args=parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(verify(args.n),args.output)

if __name__=='__main__':
    try:
        main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:
        raise SystemExit(str(exc))
