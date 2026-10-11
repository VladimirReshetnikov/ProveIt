"""Exact rational/polynomial checks. These supplement, not replace, the proofs."""
from __future__ import annotations
import json
from pathlib import Path
from fractions import Fraction
from collections import Counter
import sympy as S

A,X,s=S.symbols('A X s')
counts=Counter()

def check(expr,category):
    if S.cancel(expr)!=0:
        raise AssertionError((category,expr))
    counts[category]+=1

def nu(d):return 0 if d==0 else 2*d-1

def P(d):
    out={-1:S.Integer(1)}
    if d:
        out[0]=S.Rational(1,2)
        for k in range(1,d):out[2*k-1]=S.bernoulli(2*k)/S.factorial(2*k)
    return out

def zv(k,C):
    if k<=0:return -S.bernoulli(1-k,C)/(1-k)
    raise ValueError('only nonpositive special values')

def rz(k,C,delta=0):
    if k<=0:return (-1)**(-k)/S.factorial(-k)*zv(k+delta,C)
    if k+delta==1:return S.factorial(k-1)
    return S.Integer(0)

def re(k,C):
    return (-1)**(-k)*C**(-k)/S.factorial(-k) if k<=0 else S.Integer(0)

def residue(w,d,e,p=1,q=1):
    p,q=S.Integer(p),S.Integer(q)
    r=p*q
    ans=S.Integer(0)
    for i in range(int(p)):
        for j in range(int(q)):
            c=(A+q*i+p*j)/r
            ans+=r**(-w)*(rz(w,c,-1)+(1-c)*rz(w,c))
    for k,c in P(e).items():ans-=c*p**k*q**(-w-k)*rz(w+k,A/q)
    for j,c in P(d).items():ans-=c*q**j*p**(-w-j)*rz(w+j,A/p)
    for j,c in P(d).items():
        for k,v in P(e).items():ans+=c*v*q**j*p**k*re(w+j+k,A)
    return S.expand(ans)

def main():
    # Formal reciprocal of (1-exp(-X))/X, computed with rational recurrence.
    N=28
    f=[Fraction((-1)**n,S.factorial(n+1)) for n in range(N+1)]
    inv=[Fraction(1)]
    for n in range(1,N+1):inv.append(-sum(f[k]*inv[n-k] for k in range(1,n+1)))
    for d in range(7):
        vals={j:S.Rational(inv[j+1].numerator,inv[j+1].denominator)
              for j in range(-1,N)}
        for j,c in P(d).items():vals[j]-=c
        if any(vals[j]!=0 for j in range(-1,nu(d))):raise AssertionError('valuation')
        if vals[nu(d)]==0:raise AssertionError('leading coefficient')
        counts['kernel_valuation_certificates']+=1
    # Compensated spectral zeros: the Gamma factor cannot be discarded.
    for d in range(1,7):
        for n in range(nu(d)):
            R=zv(-n,A)+A**(n+1)/(n+1)-A**n/2
            for k in range(1,d):
                R-=S.bernoulli(2*k)/S.factorial(2*k)*S.rf(-n,2*k-1)*A**(n+1-2*k)
            check(R,'compensated_spectral_zeros')
    for d in range(5):
        for e in range(5):
            for w in range(-nu(d)-nu(e)+1,3):
                check(residue(w,d,e),'equal_scale_residue_cancellations')
    for p in range(1,4):
        for q in range(1,4):
            for d in range(3):
                for e in range(3):
                    for w in [0,1,2]:
                        if w>-nu(d)-nu(e):
                            check(residue(w,d,e,p,q),'rational_scale_residue_cancellations')
    for p in range(1,8):
        for q in range(1,8):
            num=sum(X**(q*i+p*j) for i in range(p) for j in range(q))
            check((1-X**(p*q))**2-num*(1-X**p)*(1-X**q),
                  'rational_lattice_polynomial_certificates')
    # The zero and finite part yielding the explicit Stirling pairing.
    Bminus=2*zv(-2,A)-A*zv(-1,A)+A**3/6-A**2/2+A/4
    check(Bminus,'stirling_zero_and_polynomial_reduction')
    poly=-zv(-2,A)/2-5*A**3/36+A**2/4-A**3/36-A/12
    check(poly,'stirling_zero_and_polynomial_reduction')
    result={'status':'PASS','exact_assertions':sum(counts.values()),
            'categories':dict(counts),'sympy_version':S.__version__,
            'interpretation':'Finite algebraic checks only; analytic proof is in article.tex.'}
    out=Path(__file__).resolve().parents[1]/'results'/'exact_checks.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
