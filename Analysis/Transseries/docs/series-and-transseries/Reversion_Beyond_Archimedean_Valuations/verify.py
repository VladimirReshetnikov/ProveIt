#!/usr/bin/env python3
"""Exact finite checks for Reversion Beyond Archimedean Valuations.

Python 3.10+, SymPy. No numerical approximations or network access.
These checks audit examples and identities, not the universal theorems.
Run: python verify.py [--output verification_results.json]
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial
from pathlib import Path
import json
import platform
import sympy as sp


def scalar_newton_check(limit: int = 130) -> dict:
    """Newton for U+z/(1+U), explicitly NOT for U^2+U+z."""
    def add(a, b): return [x+y for x,y in zip(a,b)]
    def neg(a): return [-x for x in a]
    def mul(a,b):
        c=[Q(0)]*(limit+1)
        for i,x in enumerate(a):
            if x:
                for j in range(limit+1-i):
                    if b[j]: c[i+j]+=x*b[j]
        return c
    def inv(a):
        if a[0] == 0: raise ZeroDivisionError("series has zero constant")
        b=[1/a[0]]+[Q(0)]*limit
        for n in range(1,limit+1):
            b[n]=-sum(a[j]*b[n-j] for j in range(1,n+1))/a[0]
        return b
    one=[Q(1)]+[Q(0)]*limit
    z=[Q(0),Q(1)]+[Q(0)]*(limit-1)
    root=[Q(0)]+[-Q(comb(2*(m-1),m-1),m) for m in range(1,limit+1)]
    assert add(root,mul(z,inv(add(one,root)))) == [0]*(limit+1)
    u=[Q(0)]*(limit+1)
    rows=[]
    for n in range(7):
        e=add(u,neg(root))
        lead=next(i for i,x in enumerate(e) if x)
        expected=2**(n+1)-1
        assert lead == expected and e[lead] == 1
        rows.append({"newton_index":n,"first_error_degree":lead,
                     "leading_error_coefficient":str(e[lead]),
                     "displacement_error_valuation_multiple_of_h":2*lead-1})
        if n < 6:
            reciprocal=inv(add(one,u))
            residual=add(u,mul(z,reciprocal))
            jacobian=add(one,neg(mul(z,mul(reciprocal,reciprocal))))
            u=add(u,neg(mul(residual,inv(jacobian))))
    return {"truncation_degree":limit,"root_residual_zero":True,"rows":rows}


L=sp.Symbol('L')
ZERO=sp.Poly(0,L,domain=sp.QQ)
ONE=sp.Poly(1,L,domain=sp.QQ)
D=6
Series=dict[tuple[int,int],sp.Poly]


def clean(a:Series)->Series:
    return {m:p for m,p in a.items() if p and sum(m)<=D}

def plus(*series:Series)->Series:
    a:Series={}
    for s in series:
        for m,p in s.items(): a[m]=a.get(m,ZERO)+p
    return clean(a)

def scale(a:Series,c)->Series:
    return clean({m:p*c for m,p in a.items()})

def times(a:Series,b:Series)->Series:
    c:Series={}
    for m,p in a.items():
        for n,q in b.items():
            k=(m[0]+n[0],m[1]+n[1])
            if sum(k)<=D: c[k]=c.get(k,ZERO)+p*q
    return clean(c)

def power(a:Series,n:int)->Series:
    if n<0: raise ValueError("nonnegative integer power required")
    out={(0,0):ONE}
    for _ in range(n): out=times(out,a)
    return out

def binomial_series(u:Series,a)->Series:
    if (0,0) in u: raise ValueError("binomial input must have zero constant")
    out={(0,0):ONE}; p={(0,0):ONE}; c=sp.Rational(1)
    for j in range(1,D+1):
        p=times(p,u); c=c*(a-j+1)/j
        out=plus(out,scale(p,c))
    return out

def logarithm(u:Series)->Series:
    out:Series={}; p={(0,0):ONE}
    for j in range(1,D+1):
        p=times(p,u); out=plus(out,scale(p,sp.Rational((-1)**(j+1),j)))
    return out

def polynomial_substitute(p:sp.Poly,ell:Series)->Series:
    out:Series={}
    for c in p.all_coeffs(): out=plus(times(out,ell),{(0,0):sp.Poly(c,L,domain=sp.QQ)})
    return out

def shift(a:Series,m:tuple[int,int])->Series:
    return clean({(n[0]+m[0],n[1]+m[1]):p for n,p in a.items()})

def chi(m:tuple[int,int])->int:
    # s1=(0,2), s2=(1,-3) in lexicographic Z^2, chi(a,b)=b.
    return 2*m[0]-3*m[1]

INPUTS=[((1,0),sp.Poly(L+1,L)),
        ((0,1),sp.Poly(L**2-2,L)),
        ((1,1),sp.Poly(L,L))]  # s3=s1+s2: a genuine resonance.


def feedback(u:Series,derivative:bool=False)->Series:
    ell=plus({(0,0):sp.Poly(L,L)},logarithm(u))
    out:Series={}
    for m,p in INPUTS:
        if derivative:
            q=p.diff()+(1-chi(m))*p
            exponent=-chi(m)
        else:
            q=p; exponent=1-chi(m)
        term=times(binomial_series(u,sp.Rational(exponent)),polynomial_substitute(q,ell))
        out=plus(out,shift(term,m))
    return out


def substitution(f:Series,b:Series)->Series:
    ell=plus({(0,0):sp.Poly(L,L)},logarithm(b))
    out:Series={}
    for m,p in f.items():
        term=times(binomial_series(b,sp.Rational(-chi(m))),polynomial_substitute(p,ell))
        out=plus(out,shift(term,m))
    return out


def resonant_power_log_check()->dict:
    b=plus(*[{m:p} for m,p in INPUTS])
    lagrange:Series={}; bn={(0,0):ONE}
    for n in range(1,D+1):
        bn=times(bn,b)
        term:Series={}
        for m,p in bn.items():
            q=p
            for j in range(n-1): q=q.diff()-(chi(m)-n+j)*q
            term[m]=q*sp.Rational((-1)**n,factorial(n))
        lagrange=plus(lagrange,term)
    assert not plus(lagrange,feedback(lagrange))
    # Reverse composition, normalized: b+(1+b) (U o (X+B)).
    reverse=plus(b,times(plus({(0,0):ONE},b),substitution(lagrange,b)))
    assert not reverse
    picard:Series={}
    for _ in range(D): picard=scale(feedback(picard),-1)
    assert picard == lagrange
    newton:Series={}; rows=[]
    for n in range(3):
        err=plus(newton,scale(lagrange,-1))
        actual=min((sum(m) for m in err),default=None)
        bound=2**(n+1)-1
        assert actual is None or actual>=bound
        rows.append({"newton_index":n,"promised_error_depth":bound,
                     "first_nonzero_total_degree_within_test":actual})
        if n<2:
            residual=plus(newton,feedback(newton))
            correction=times(residual,binomial_series(feedback(newton,True),sp.Rational(-1)))
            newton=plus(newton,scale(correction,-1))
    assert newton == lagrange
    chosen={str(m):str(lagrange.get(m,ZERO).as_expr())
            for m in [(1,0),(0,1),(1,1),(2,0),(0,2),(2,1)]}
    return {"total_degree_cutoff":D,"nonzero_blocks":len(lagrange),
            "input_resonance":"s3 = s1 + s2", "lagrange_residual_zero":True,
            "reverse_composition_residual_zero":True,"picard_agrees":True,
            "newton_agrees":True,"newton_rows":rows,"selected_coefficients":chosen}


def finite_certificate_check()->dict:
    generators=[(0,1),(1,-2),(1,0)]
    target=(2,1)
    w=lambda a:3*a[0]+a[1]
    assert all(w(s)>=1 for s in generators)
    budget=w(target)
    representations=[]
    for counts in product(range(budget+1),repeat=3):
        if sum(counts)>budget: continue
        alpha=tuple(sum(counts[i]*generators[i][j] for i in range(3)) for j in range(2))
        if alpha==target: representations.append(counts)
    assert representations == [(1,0,2),(3,1,1),(5,2,0)]
    divisors=set()
    for c in representations:
        for a in product(*(range(x+1) for x in c)):
            divisors.add(tuple(sum(a[i]*generators[i][j] for i in range(3)) for j in range(2)))
    depth=max(map(sum,representations))
    assert depth == 7
    # Exact downward-closure audit inside this finite monoid ideal.
    for alpha in list(divisors):
        if alpha == (0,0): continue
        for s in generators:
            beta=(alpha[0]-s[0],alpha[1]-s[1])
            # This monoid equals { (a,b): a>=0, b>=-2a }.
            if beta[0]>=0 and beta[1]>=-2*beta[0]: assert beta in divisors
    return {"generators":generators,"target":target,"functional":[3,1],
            "functional_generator_values":[w(s) for s in generators],
            "word_budget":budget,"representations":representations,
            "exact_depth":depth,"divisor_quotient_rank":len(divisors),
            "divisor_exponents":sorted(divisors),"downward_closed":True}


def partitions(n:int,largest:int|None=None):
    if n==0:
        yield ()
        return
    if largest is None: largest=n
    for a in range(min(largest,n),0,-1):
        for rest in partitions(n-a,a): yield (a,)+rest


def infinite_support_check()->dict:
    tests=0; sample=[]
    for n in range(1,11):
        ps=list(partitions(n))
        for k in range(-n*n,11):
            lengths=[k+sum(a*a for a in p)+len(p) for p in ps
                     if k+sum(a*a for a in p)>=0]
            predicted=n*n+k+1
            assert lengths and max(lengths)==predicted
            # The target-dependent rational separator attains the same bound.
            weight_eta=Q(n*n+1,n)
            assert all(j*weight_eta-j*j >= 1 for j in range(1,n+1))
            assert n*weight_eta+k == predicted
            tests+=1
        sample.append({"target":[n,0],"exact_depth":n*n+1,
                       "sufficient_newton_index":(n*n+2).bit_length()-1})
    return {"support":"{(0,1)} union {(n,-n^2): n>=1}",
            "positive_first_coordinates_tested":[1,10],
            "second_coordinate_range":"-n^2 <= k <= 10",
            "exact_depth_checks":tests,"eta_ray_samples":sample}



def factorial_profile_check()->dict:
    """Independent partition enumeration for the superadditive profile n!."""
    tests=0
    for n in range(1,10):
        bn=factorial(n)
        ks=sorted({1-bn,2-bn,-1,0,1,5})
        for k in ks:
            if k < 1-bn: continue
            feasible=[]
            for part in partitions(n):
                delta_count=k+sum(factorial(j)-1 for j in part)
                if delta_count>=0: feasible.append(delta_count+len(part))
            assert feasible and max(feasible)==k+bn
            tests+=1
    return {"profile":"b_n=n!", "first_coordinate_range":[1,9],
            "target_rule":"k in {1-n!,2-n!,-1,0,1,5}, retaining k>=1-n!",
            "exact_depth_checks":tests}


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',default='verification_results.json')
    args=parser.parse_args()
    results={"status":"all exact finite checks passed", "python":platform.python_version(),
             "sympy":sp.__version__,"arithmetic":"rational and polynomial; no floating point",
             "scope":"Finite example audits; not a formal proof of the universal statements.",
             "sharp_scalar_newton":scalar_newton_check(),
             "resonant_power_log":resonant_power_log_check(),
             "finite_quotient_certificate":finite_certificate_check(),
             "infinite_support_depth":infinite_support_check(),
             "factorial_profile_depth":factorial_profile_check()}
    # ProveIt edit (2026-09-29): write LF on every platform.
    Path(args.output).write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(results['status'])
    print('Scalar Newton depths:',[r['first_error_degree'] for r in results['sharp_scalar_newton']['rows']])
    print('Power-log blocks:',results['resonant_power_log']['nonzero_blocks'])
    print('Finite quotient rank:',results['finite_quotient_certificate']['divisor_quotient_rank'])
    print('Infinite-support depth checks:',results['infinite_support_depth']['exact_depth_checks'])
    print('Factorial-profile depth checks:',results['factorial_profile_depth']['exact_depth_checks'])
    print('Wrote',args.output)

if __name__=='__main__': main()
