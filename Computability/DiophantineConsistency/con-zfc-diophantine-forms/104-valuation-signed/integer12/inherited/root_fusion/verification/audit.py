#!/usr/bin/env python3
"""Exact comparison against an independently ordered formal conjugate product."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
import json, time, hashlib
from five_square_norm import five_square_norm, four_square_norm, three_square_norm

ROOT=Path(__file__).resolve().parent
NAMES=('x','a','b','c','d','e')
ZERO=(0,0,0,0,0,0,0)  # six integral exponents, followed by root parity mask

class Poly:
    def __init__(self, terms=None):self.terms=terms or {}
    @staticmethod
    def scalar(n):return Poly({ZERO:n}) if n else Poly()
    @staticmethod
    def variable(j):
        m=list(ZERO);m[j]=1;return Poly({tuple(m):1})
    @staticmethod
    def radical(j):
        m=list(ZERO);m[-1]=1<<j;return Poly({tuple(m):1})
    @staticmethod
    def coerce(p):return p if isinstance(p,Poly) else Poly.scalar(p)
    def __add__(self,p):
        p=self.coerce(p);out=dict(self.terms)
        for m,c in p.terms.items():
            out[m]=out.get(m,0)+c
            if not out[m]:del out[m]
        return Poly(out)
    def __radd__(self,p):return self+p
    def __neg__(self):return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self,p):return self+(-self.coerce(p))
    def __rsub__(self,p):return self.coerce(p)+(-self)
    @staticmethod
    def product_monomial(m,n):
        common=m[6]&n[6]
        return (m[0]+n[0],m[1]+n[1]+(common&1),
          m[2]+n[2]+((common>>1)&1),m[3]+n[3]+((common>>2)&1),
          m[4]+n[4]+((common>>3)&1),m[5]+n[5]+((common>>4)&1),m[6]^n[6])
    def __mul__(self,p):
        p=self.coerce(p);out={};add=out.get;prod=self.product_monomial
        if p is self:
            items=list(self.terms.items())
            for i,(m,c) in enumerate(items):
                u=prod(m,m);out[u]=add(u,0)+c*c
                for n,e in items[i+1:]:
                    u=prod(m,n);out[u]=add(u,0)+2*c*e
        else:
            for m,c in self.terms.items():
                for n,e in p.terms.items():
                    u=prod(m,n);out[u]=add(u,0)+c*e
        return Poly({m:c for m,c in out.items() if c})
    def __rmul__(self,p):return self*p
    def conjugate(self,j):return Poly({m:(-c if m[6]&(1<<j) else c) for m,c in self.terms.items()})

def audit_norm(k):
    start=time.monotonic()
    x,a,b,c,d,e=(Poly.variable(j) for j in range(6))
    fast={3:lambda:three_square_norm(x,a,b,c),4:lambda:four_square_norm(x,a,b,c,d),
          5:lambda:five_square_norm(x,a,b,c,d,e)}[k]()
    # Independent defining product. Conjugation order is the reverse of
    # the optimized construction; no F8 formula or biquadratic squarer is used.
    product=x
    for j in range(k):product=product-Poly.radical(j)
    for j in reversed(range(k)):
        product=product*product.conjugate(j)
    if fast.terms!=product.terms:raise ValueError(f'{k}-radical exact identity failed')
    if any(m[-1] for m in product.terms):raise ValueError('uneliminated radical')
    expected_degree=2**k
    if any(m[0]+2*sum(m[1:6])!=expected_degree for m in fast.terms):raise ValueError('weighted degree')
    lead=(expected_degree,0,0,0,0,0,0)
    if fast.terms.get(lead)!=1:raise ValueError('not monic in x')
    # Invariance under permutation of all k radicands is checked on the
    # exact final coefficient dictionary, providing another independent check.
    for i in range(1,k):
        swapped={}
        for m,c0 in fast.terms.items():
            n=list(m);n[i],n[i+1]=n[i+1],n[i]
            swapped[tuple(n)]=c0
        if swapped!=fast.terms:raise ValueError('radicand symmetry failed')
    canonical=json.dumps([[list(m),c0] for m,c0 in sorted(fast.terms.items())],separators=(',',':'))
    if k==5:(ROOT/'five_square_norm_expanded.json').write_text(json.dumps({
        'variables':list(NAMES),'terms':[[list(m[:6]),c0] for m,c0 in sorted(fast.terms.items())],
        'definition':'Product over all 32 independent sign choices of x-sum(sign_i*sqrt(A_i)).',
        'weighted_degree':32},indent=2)+'\n')
    return {'radicands':k,'monomials':len(fast.terms),'weighted_degree':expected_degree,
        'monic_x_degree':expected_degree,'coefficient_sha256':hashlib.sha256(canonical.encode()).hexdigest(),
        'exact_checks':['optimized expression equals reverse-order formal conjugate product',
          'all radical parity masks vanish','all adjacent radicand permutations preserve coefficients',
          'weighted homogeneity and monic leading coefficient'],
        'seconds':round(time.monotonic()-start,3)}

def main():
    results=[]
    for k in (3,4,5):
        result=audit_norm(k);results.append(result);print(json.dumps(result),flush=True)
    (ROOT/'EXACT_AUDIT.json').write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
