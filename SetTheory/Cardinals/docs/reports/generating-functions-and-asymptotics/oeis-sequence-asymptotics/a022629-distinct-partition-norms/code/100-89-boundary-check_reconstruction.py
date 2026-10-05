#!/usr/bin/env python3
"""Independent profile enumeration for Edgeworth and Bernoulli recursion."""
import json, pathlib
import sympy as s
ROOT=pathlib.Path(__file__).resolve().parent
SRC=ROOT
p,x=s.symbols('p x')
v=s.symbols('v',positive=True)
ks={j:s.Symbol('k'+str(j)) for j in range(3,9)}

def profiles(weights,total):
    if not weights:
        yield (); return
    for m in range(total//weights[0]+1):
        for tail in profiles(weights[1:],total-m*weights[0]):
            yield (m,)+tail

def gaussian_profiles(M):
    if M==0: return s.Integer(1)
    out=0
    for ms in profiles(tuple(range(1,2*M+1)),2*M):
        W=sum((j-2)*m for j,m in zip(range(3,2*M+3),ms))
        if W!=2*M: continue
        J=sum(j*m for j,m in zip(range(3,2*M+3),ms))
        if J%2:continue
        term=(-1)**(J//2)*s.factorial2(J-1)
        for j,m in zip(range(3,2*M+3),ms):
            term*=ks[j]**m/(s.factorial(j)**m*s.factorial(m)*v**s.Rational(j*m,2))
        out+=term
    return s.factor(out)

def boundary_one(r):
    # Bernoulli cumulants are recursively generated in probability p,
    # rather than applying powers of y*d/dy to log(1+y).
    k=p
    for _ in range(1,r):k=s.expand(p*(1-p)*s.diff(k,p))
    f=s.cancel((-x)**r*k.subs(p,x/(1+x)))
    # Expand at x+1=0 after polynomial division; every remaining pole is -1.
    numerator,denominator=s.fraction(f)
    polynomial,remainder=s.div(numerator,denominator,x)
    value=sum(c*s.zeta(-degree[0]) for degree,c in s.Poly(polynomial,x).terms())
    y=s.symbols('y')
    poles=s.Poly(s.cancel((remainder/denominator).subs(x,y-1)*y**r),y)
    for (degree,),c in poles.terms():
        j=r-degree
        if j<=0:raise RuntimeError('invalid partial fraction')
        term=-s.digamma(2) if j==1 else s.zeta(j,2)-s.Rational(1,j-1)
        value+=c*term
    return s.simplify(value/s.factorial(r))

def main():
    producer=json.loads((SRC/'check_corrections.json').read_text())
    namespace={'v':v,**{str(k):k for k in ks.values()}}
    edges={}
    for M in range(4):
        own=gaussian_profiles(M)
        previous=s.sympify(producer['edgeworth'][str(M)],locals=namespace)
        if s.simplify(own-previous)!=0:raise RuntimeError(('Edgeworth mismatch',M))
        edges[M]=str(own)
    coeffs={}
    for r in range(1,7):
        own=boundary_one(r)
        previous=s.sympify(producer['boundary_a1'][str(r)])
        if s.simplify(own-previous)!=0:raise RuntimeError(('boundary mismatch',r))
        coeffs[r]=str(own)
    result={'status':'pass','method':'independent cumulant recursion and weighted multiindex enumeration',
            'boundary_coefficients':coeffs,'edgeworth_homogeneous_blocks':edges,
            'exact_comparisons':10}
    (ROOT/'reconstruction.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
