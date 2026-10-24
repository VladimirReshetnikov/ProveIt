#!/usr/bin/env python3
"""Exact algebra and finite regression for the index-free inert-prime closure."""
from math import comb,factorial,gcd,prod
from pathlib import Path
import json
import sympy as sp
import argparse
_parser=argparse.ArgumentParser(description=__doc__)
_parser.add_argument('--check', action='store_true', help='Verify sealed JSON artifacts without modifying them')
CHECK_ONLY=_parser.parse_args().check
HERE=Path(__file__).resolve().parent

def save_json(path, value):
    data=json.dumps(value, indent=2)+'\n'
    if CHECK_ONLY:
        require(path.is_file(), 'missing sealed artifact: '+str(path))
        require(path.read_text()==data, 'sealed artifact differs: '+str(path))
    else:
        path.write_text(data)

def require(condition,message):
    if not condition:raise RuntimeError(message)
def norm(xs):
    if len(xs)==1:return xs[0]
    k=len(xs)//2
    return norm(xs[:k])**2+norm(xs[k:])**2
def crt(rs,ms):
    B=prod(ms)
    return sum(r*(B//m)*pow(B//m,-1,m) for r,m in zip(rs,ms))%B if B>1 else 0

i,D,a,b,x=sp.symbols('i D a b x')
polynomials=[a-i,(a-i)**2+(b-i-1)**2,x*i**3+a*i**2-b*i+7,a**4-b**3]
identities=[]
for P in polynomials:
    poly=sp.Poly(P,i);d=poly.degree();R=0;quotient=0
    for (k,),coefficient in poly.terms():
        R+=coefficient*D**(d-k)*(1-D)**k
        quotient-=coefficient*D**(d-k)*sum((1-D)**(k-1-r)*(D*i)**r for r in range(k))
    require(sp.expand(R-D**d*P-(D*(i+1)-1)*quotient)==0,'denominator-clearing identity')
    identities.append({'source':str(sp.expand(P)),'index_degree':d,'cleared':str(sp.expand(R)),'divisibility_quotient':str(sp.expand(quotient))})
checks={};k=0
for H in range(1,13):
    T=factorial(H);D0=4*T
    for n in range(H+1):
        F=factorial(n);E=D0**n;S=E*F;Q=S;M=D0*Q+1
        ms=[D0*j-1 for j in range(1,n+1)];B=prod(ms)
        require(B<M,'remainder bound')
        require(S*comb(Q+n,n)%M==B,'new exact product formula')
        require(all(gcd(u,v)==1 for j,u in enumerate(ms) for v in ms[j+1:]),'pairwise coprime')
        require(all(m%4==3 for m in ms),'inert congruence class')
        if n:require(B<S,'sharp product bound')
        k+=1
checks['exact_product_cases_including_empty_bound']=k
k=0
for p in [3,7,11,19,23,31]:
    for u in range(p):
        for v in range(p):
            require(((u*u+v*v)%p==0)==(u==v==0),'anisotropy')
            k+=1
checks['anisotropic_prime_pairs']=k
# A genuine polynomial family with two shared CRT coordinate witnesses.
n=3;U=3
e=lambda i,w1,w2:w1*w1+i*i+w2*w2+(i+1)**2
f=lambda i,w1,w2:2*i*w1+2*(i+1)*w2
H=e(n,U,U)+f(n,U,U)+n+U+1;T=factorial(H);D0=4*T
ms=[D0*(j+1)-1 for j in range(n)];B=prod(ms)
A1=crt(list(range(n)),ms);A2=crt(list(range(1,n+1)),ms)
Rpoly=sp.Poly(polynomials[1],i);d=Rpoly.degree()
R=sum(int(c.subs({a:A1,b:A2}))*D0**(d-k)*(1-D0)**k for (k,),c in Rpoly.terms())
leaves=[comb(A1,U+1),comb(A2,U+1),R]
require(norm(leaves)%B==0,'complete bounded-family fixture')
checks['two_coordinate_complete_fixture']=True
# Exact reductions over finite fields, including the index-free substitution.
k=0
for p in [7,11,19,23,31]:
    U=2
    for D0 in range(1,p):
        index=(pow(D0,-1,p)-1)%p
        for A in range(p):
            R=D0*A-(1-D0)
            # Soundness is about the unique congruent index; range picks 0..U.
            P=norm([comb(A,U+1),R])%p
            require((P==0)==(A<=U and A==index),'index-free range and local relation')
            k+=1
checks['index_free_range_residual_cases']=k
# Omitting denominator clearing does not preserve congruence, and finite-field
# isotropy at a split prime is not acceptable.
require((1+2*2)%5==0,'negative split-prime control')
require(norm([0,7])%7==0 and 7!=0,'negative missing-size-bound control')
checks['negative_controls']=2
report={'status':'PASS','scope':'Exact polynomial identities and finite arithmetic controls, not a Lean theorem or compiled ordinary global polynomial.','checks':checks,'symbolic_index_eliminations':identities,'special_function_interface':{'old_power_graph_calls':2,'new_power_graph_calls':1,'factorial_graph_calls':2,'binomial_graph_calls':'m+1','old_outer_crt_coordinates':'m+2','new_outer_crt_coordinates':'m+1','conditional_natural_witness_count':'2m+9+2*f+p+(m+1)*b, if factorial/power/binomial graphs have f/p/b internal witnesses beyond their visible inputs and output'}}
save_json(HERE/'CRT_CHECK_RESULTS.json', report)
print(json.dumps(report,indent=2))
