#!/usr/bin/env python3
"""Generate exact positive cubature using rational least-squares correction.
Dependencies: numpy, sympy. No floating point enters the certificate.
"""
import itertools, json, math
from pathlib import Path
import numpy as np
import sympy as sp
from fractions import Fraction

ROOT = Path(__file__).resolve().parent
Q = [3,5,7,11,13,17,19,23]
K = 2
X = 100000
A = [s for j in range(K+1) for s in itertools.combinations(range(len(Q)), j)]

def v(p):
    u = [1 if pow(q, (p-1)//2, p)==1 else -1 for q in Q]
    return [math.prod(u[i] for i in s) for s in A]

def raw(p):
    return (p-X)**2*(2*X-p)**2

def main():
    primes = list(map(int,sp.primerange(X+1,2*X)))
    z = sum(map(raw,primes))
    # Delete a sign-biased selection, taking largest baseline weights first.
    eligible = sorted((p for p in primes if v(p)[1]==1 and v(p)[2]==1),key=lambda p:(-raw(p),p))
    deleted=[]; lost=0
    for p in eligible:
        if 100*(lost+raw(p)) <= 2*z:
            deleted.append(p);lost+=raw(p)
    survivors=[p for p in primes if p not in set(deleted)]
    w = np.array([raw(p) for p in survivors],dtype=object)
    V = np.array([v(p) for p in survivors],dtype=object)
    G=sp.Matrix((V.T@(w[:,None]*V)).tolist())
    rhs=sp.Matrix([sum(w)]+[0]*(len(A)-1))
    c=list(G.inv()*rhs)
    values=[sum(int(x)*y for x,y in zip(row,c)) for row in V]
    assert min(values)>=sp.Rational(3,4) and max(values)<=sp.Rational(5,4), (float(min(values)),float(max(values)))
    # Factors c.v(p) multiply the normalized rational bump masses.
    cert=dict(q=Q,k=K,X=X,deleted=deleted,coefficients=[str(x) for x in c],
              count=len(primes),survivors=len(survivors))
    (ROOT/'certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    print('primes:',len(primes),'survivors:',len(survivors),'dimension:',len(A))
    print('deleted baseline fraction:',float(Fraction(lost,z)))
    print('min/max weight ratio:',float(min(values)),float(max(values)))

if __name__=='__main__':main()
