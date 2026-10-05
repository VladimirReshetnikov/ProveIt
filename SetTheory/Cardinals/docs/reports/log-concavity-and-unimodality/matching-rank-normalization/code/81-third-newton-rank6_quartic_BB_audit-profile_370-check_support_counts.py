#!/usr/bin/env python3
"""Exact endpoint-set polynomial check for the BB (3,7,0) aggregates."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations
from pathlib import Path
import hashlib,json,math
import sympy as s

HERE=Path(__file__).resolve().parent
MASKS=(1,2,3,5,6,7)
NV=s.symbols('N1 N2 N3 N5 N6 N7')
VARIABLE=dict(zip(MASKS,NV))
CORE=(3,3,2)


@lru_cache(None)
def matched(rows):
    return any(all(mask&(1<<j) for mask,j in zip(rows,assignment))
               for assignment in permutations(range(len(rows))))


def project(mask,columns):
    return sum(1<<i for i,col in enumerate(columns) if mask&(1<<col))


@lru_cache(None)
def population_weight(rows):
    result=s.Integer(1)
    for mask,k in Counter(rows).items():
        n=VARIABLE[mask]
        result*=s.prod(n-i for i in range(k))/math.factorial(k)
    return s.expand(result)


def endpoint_count(columns,S=0,T=0):
    degree=len(columns)
    A=tuple(CORE[i]+(8 if S&(1<<i) else 0)+(16 if T&(1<<i) else 0)
            for i in range(3))
    result=s.Integer(0)
    for ell in range(degree+1):
        if degree-ell>3:
            continue
        for L in combinations_with_replacement(MASKS,ell):
            count=0
            for selected in combinations(range(3),degree-ell):
                rows=tuple(project(mask,columns) for mask in L+tuple(A[i] for i in selected))
                count+=matched(tuple(sorted(rows)))
            if count:
                result+=count*population_weight(L)
    return s.expand(result)


def pure_count(columns,extra=()):
    count=len(columns)-len(extra)
    result=s.Integer(0)
    for L in combinations_with_replacement(MASKS,count):
        rows=tuple(project(mask,columns) for mask in L+extra)
        if matched(tuple(sorted(rows))):
            result+=population_weight(L)
    return s.expand(result)


def hp(S,T):
    return sum(any(S&(1<<i) and T&(1<<j) for i,j in permutations(I))
               for I in combinations(range(3),2))


def cp(S,T,U):
    return int(any(all(mask&(1<<j) for mask,j in zip((S,T,U),P))
                   for P in permutations(range(3))))


checked=[]
def equal(label,left,right):
    difference=s.Poly(s.expand(left-right),*NV)
    if not difference.is_zero:
        raise ArithmeticError((label,str(difference.as_expr())))
    checked.append(label)


N1,N2,N3,N5,N6,N7=NV
m=sum(NV);u=N1+N3+N5+N7;z=N5+N6+N7;v=N5+N7;c=N3+N7
p=u*(m-u)+u*c-c*(c+1)/2
h=m*z-z*(z+1)/2
g=u*z-v*(v+1)/2
q=pure_count((0,1,2))
equal('p',pure_count((0,1)),p)
equal('h',pure_count((0,1,2),(3,)),h)
equal('g',pure_count((0,2)),g)
equal('E',endpoint_count((0,1)),p+2*m+u+3)
equal('x',endpoint_count((0,1,2)),q+2*h+g+3*z)
for S in range(1,8):
    G=int(bool(S&1))+int(bool(S&2))-int(S&5==5)-int(S&6==6)
    equal(('r',S),endpoint_count((0,1,3),S),p*S.bit_count()+u*hp(7,S)+(m-u)*hp(3,S)+1)
    equal(('v',S),endpoint_count((0,1,2,3),S),q*S.bit_count()+h*hp(3,S)+g*G+z)
    for T in range(S,8):
        equal(('b',S,T),endpoint_count((0,1,3,4),S,T),
              p*hp(S,T)+u*cp(7,S,T)+(m-u)*cp(3,S,T))
record={'status':'pass','profile':[3,7,0],'exact_polynomial_identities':len(checked),
        'method':'explicit injective coordinate assignments and distinct endpoint sets',
        'checked':checked,'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'support_count_certificate.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
