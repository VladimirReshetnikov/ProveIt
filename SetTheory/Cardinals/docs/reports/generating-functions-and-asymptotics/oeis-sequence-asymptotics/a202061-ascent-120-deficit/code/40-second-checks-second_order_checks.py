#!/usr/bin/env python3
"""Deterministic symbolic and finite checks; not a replacement for the proofs."""
from fractions import Fraction
from itertools import product
from collections import Counter
import sympy as s

alpha,v,B,u,H,C0,x,t,r=s.symbols('alpha v B u H C0 x t r', positive=True)
phi=x+2*s.log(x)-C0
expected=2*x+4*s.log(x)-2*C0-3-6/x-2/x**2
assert s.simplify(s.diff(phi,x,2)-3*s.diff(phi,x)+2*phi-expected)==0
V=(s.log(H*u)+2*s.log(s.log(H*u))-C0)/u
assert s.simplify(u**3*s.diff(V,u,2)-expected.subs(x,s.log(H*u)))==0
print('PASS: exact softened-potential second derivative')

c=s.symbols('c',real=True)
Brel=1+s.Rational(7,2)*r*t+s.Rational(3,2)*c*t
expansion=s.series(Brel**s.Rational(2,3),t,0,2).removeO()
assert s.expand(expansion-1-t*(s.Rational(7,3)*r+c))==0
A=2*s.pi**2*alpha**2/v
Ccube=3*s.pi**2*alpha**2/(2*v)
assert s.simplify(6*A/8-Ccube)==0
assert s.Rational(1,6)+1==s.Rational(7,6)
assert 2*s.Rational(7,6)==s.Rational(7,3)
print('PASS: matching exact 7/3 coefficients and leading constant cubes')

angle,d=s.symbols('angle d',real=True)
lhs=s.sin(angle+d)**2-s.sin(angle)**2
rhs=s.sin(angle)*s.sin(d)*(2*s.cos(angle)*s.cos(d)+s.cos(2*angle)/s.sin(angle)*s.sin(d))
assert s.trigsimp(s.expand_trig(lhs-rhs))==0
print('PASS: exact discrete sine-square energy decomposition')

# Every retained first-order cancellation is a symmetry claim, even after
# balancing and a symmetric good-path restriction.
bs=(1,2,2,1)
limits=(1,2,2,1)
vecs=[]
for xs in product(*(range(-b,b+1) for b in bs)):
    if sum(xs):continue
    partial=0; good=True
    for a,lim in zip(xs,limits):
        partial+=a
        if abs(partial)>lim:good=False;break
    if good:vecs.append(xs)
assert vecs
for j in range(len(bs)):
    assert sum(xs[j] for xs in vecs)==0
assert set(vecs)=={tuple(-a for a in xs) for xs in vecs}
print(f'PASS: centered good balanced bridge marginals ({len(vecs)} exact vectors)')

nchecks=0
for k in range(1,5):
    for widths in product(range(4),repeat=k):
        counts=Counter({0:1})
        for w in widths:
            out=Counter()
            for old,num in counts.items():
                for j in range(-w,w+1):out[old+j]+=num
            counts=out
        peak=counts[0]
        assert peak==max(counts.values())
        assert peak*(2*sum(widths)+1)>=sum(counts.values())
        assert all(counts[j]==counts[-j] for j in counts)
        nchecks+=1
print(f'PASS: {nchecks} exact symmetric-unimodal central-count diagnostics')

# Conditional length vectors need not be independent across coordinates.
# Symmetry suffices for the one-coordinate reciprocal estimate.
ell=Fraction(30);width=3
for lengths in [(width,width),(width,2,width),(1,width,2,width)]:
    us=[xs for xs in product(*(range(-w,w+1) for w in lengths)) if sum(xs)==0]
    for j in range(len(lengths)):
        assert sum(xs[j] for xs in us)==0
        er=sum((1/(ell+xs[j]) for xs in us),Fraction())/len(us)
        bound=(1/ell)*(1+Fraction(lengths[j]**2,1)/(ell**2*(1-Fraction(lengths[j],1)/ell)))
        assert er<=bound
print('PASS: exact balanced-box reciprocal second-order bound')

# The polynomial-logarithmic row remainder exponents are negative in n.
assert s.Rational(1,3)+2*s.Rational(2,3)-2==-s.Rational(1,3)
assert s.Rational(1,3)+s.Rational(1,3)-1==-s.Rational(1,3)
assert s.Rational(2,3)+3*(-s.Rational(1,3))==-s.Rational(1,3)
print('PASS: both calibration Taylor errors and cubic row remainders have n^(-1/3) gain')
print('All new deterministic checks passed; asymptotic uniformity is established in the proofs and audit.')
