#!/usr/bin/env python3
"""Exact finite checks for the accompanying article; not a proof of Hahn theorems."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s

x, a, b, z = s.symbols('x a b z')

def moment_data(poly: s.Expr):
    p=s.Poly(poly, x).monic(); n=p.degree()
    if n < 1: raise ValueError("Expected a nonconstant polynomial")
    # Companion matrix in the monomial basis 1,x,...,x^(n-1).
    M=s.zeros(n)
    for j in range(n-1): M[j+1,j]=1
    for i in range(n): M[i,n-1]=-p.nth(i)
    powers=[s.eye(n)]
    for _ in range(2*n-1): powers.append(powers[-1]*M)
    moments=[s.expand(s.trace(v)) for v in powers]
    H=s.Matrix(n,n,lambda i,j:moments[i+j])
    minors=[s.factor(H[:k,:k].det()) for k in range(1,n+1)]
    assert (M.T*H-H*M).applyfunc(s.expand)==s.zeros(n)
    assert s.factor(minors[-1]-s.discriminant(p.as_expr(),x))==0
    return M,H,minors

def valuation(expr: s.Expr) -> tuple[int,int]:
    """v(a)=(1,0), v(b)=(0,1); compare b-coordinate first (1 << omega)."""
    P=s.Poly(s.expand(expr),a,b)
    if P.is_zero: raise ValueError('zero has infinite valuation')
    return min((m for m,c in P.terms() if c!=0),key=lambda m:(m[1],m[0]))

def gf2_rank(vectors):
    basis={}
    for v in vectors:
        mask=sum((c%2)<<j for j,c in enumerate(v))
        while mask:
            bit=mask.bit_length()-1
            if bit in basis: mask^=basis[bit]
            else: basis[bit]=mask; break
    return len(basis)

def profile(minors):
    values=[(0,0)]+[valuation(h) for h in minors]
    delta=[tuple((values[j+1][i]-values[j][i])%2 for i in range(2)) for j in range(len(minors))]
    counts={str(c):delta.count(c) for c in sorted(set(delta))}
    return {'h_valuations':values[1:], 'pivot_classes':delta,'class_multiplicities':counts,
            'factor_count':delta.count((0,0)), 'splitting_degree':2**gf2_rank(delta)}

cases={
 'quadratic':x**2-a,
 'shifted_quadratic':(x-1)**2-a,
 'product_quartic':(x**2-a)*(x**2-b),
 'primitive_quartic':x**4-2*(a+b)*x**2+(a-b)**2,
 'degree_6_profile_A':(x**4-2*(a+b)*x**2+(a-b)**2)*(x-2)*(x-3),
 'degree_6_profile_B':(x**2-a)*(x**2-b)*(x**2-a*b),
}
results={}
for name,p in cases.items():
    M,H,hs=moment_data(p)
    results[name]={'polynomial':str(s.expand(p)),'hankel_minors':[str(h) for h in hs],**profile(hs)}
    print(name, json.dumps(results[name],indent=2))
assert results['quadratic']['factor_count']==1
assert results['shifted_quadratic']['factor_count']==1
assert results['product_quartic']['factor_count']==2
assert results['primitive_quartic']['factor_count']==1
assert results['product_quartic']['splitting_degree']==4
assert results['primitive_quartic']['splitting_degree']==4
assert results['degree_6_profile_A']['class_multiplicities']==results['degree_6_profile_B']['class_multiplicities']
assert results['degree_6_profile_A']['factor_count']==3
assert results['degree_6_profile_A']['splitting_degree']==4
# The positive definite 2x2 pencil.
B=s.diag(1,a); A=s.Matrix([[1,a],[a,a]])
assert s.factor((x*B-A).det()/B.det()-((x-1)**2-a))==0
assert s.factor(A.det()-a*(1-a))==0
# Quartic is precisely the product over the four sign choices.
u,v=s.symbols('u v')
root_product=s.prod(x-e*u-f*v for e in [-1,1] for f in [-1,1])
assert s.expand(root_product-(x**4-2*(u**2+v**2)*x**2+(u**2-v**2)**2))==0
# Affine covariance, checked exactly on the product quartic.
_,_,h0=moment_data(cases['product_quartic'])
_,_,h1=moment_data(s.expand(2**4*cases['product_quartic'].subs(x,(x-3)/2)))
assert all(s.factor(h1[k-1]-2**(k*(k-1))*h0[k-1])==0 for k in range(1,5))
# A repeated-root input must first be squarefree-reduced.
p_rep=s.Poly((x**2-a)**3,x)
assert s.factor(p_rep.sqf_part().as_expr()-(x*x-a))==0
# Full discriminant square need not imply trivial extension.
assert s.factor(s.discriminant(cases['primitive_quartic'],x)-4096*a*a*b*b*(a-b)**2)==0
results['checks']={'status':'PASS','scope':'Exact symbolic examples only; not a proof of infinite Hahn-field statements.',
                   'sympy_version':s.__version__}
Path(__file__).with_name('verification_results.json').write_text(json.dumps(results,indent=2)+'\n')
print('ALL EXACT SYMBOLIC CHECKS PASSED')
