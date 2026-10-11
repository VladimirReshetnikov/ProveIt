#!/usr/bin/env python3
"""Replay finite exact arithmetic and symbolic checks; not a proof assistant."""
from __future__ import annotations
import json, platform
from pathlib import Path
from math import factorial
import sympy as s
from coefficients import *

ROOT=Path(__file__).resolve().parents[1]
counts={}
def check(group, lhs, rhs):
    if s.expand(lhs-rhs)!=0:
        raise AssertionError(f'{group}: {s.expand(lhs-rhs)}')
    counts[group]=counts.get(group,0)+1

for n in range(0,9):
    for R in range(0,3):
        bound=(4,) if R==0 else ((3,2) if R==1 else (2,2,2))
        rows=[tuple(s.Rational((j+2)**r, (j+1)*(j+3)**r)
                    for r in range(R+1)) for j in range(n)]
        direct=finite_direct(rows,bound)
        exp=exp_coefficients(finite_log_coefficients(rows,bound),bound)
        for a in indices(bound):check('finite_product_vs_power_sums',direct[a],exp[a])

for n in range(1,6):
    for word in [(0,), (0,1), (1,1), (0,1,2), (0,0,1,1), (0,1,1,2)]:
        rows=[tuple(s.Rational((j+2)**r,(j+1)*(j+3)**r)
                    for r in range(3)) for j in range(n)]
        a=tuple(word.count(r) for r in range(3))
        direct=finite_direct(rows,a)[a]
        part=sum(mobius(p)*s.prod(sum(s.prod(row[word[i]] for i in B)
                                      for row in rows) for B in p)
                 for p in partitions(tuple(range(len(word)))))
        check('set_partition_identity',part,direct*s.prod(factorial(m) for m in a))

bound=(3,2,1)
P=cutoff_polynomials(bound)
C=exp_coefficients(cumulants(bound),bound)
for a in indices(bound):
    A=abel_polynomial(P[a]).subs(L,0)
    rhs=sum(C[b]*kernel_coefficient(sub(a,b)) for b in indices(a))
    check('gamma_transfer_vs_convolution',A,rhs)

bound=(9,)
P0=cutoff_polynomials(bound)
for a,poly in P0.items():
    d=a[0]
    check('a_one_unweighted_cancellation',specialize_a_one(abel_polynomial(poly)),L**d/factorial(d))

u=s.Symbol('u'); N=7
polys=cutoff_polynomials((N,1))
C0=exp_coefficients(cumulants((N,)),(N,))
B=[g(1)]+[(-1)**(j+1)*Z(j+1,1) for j in range(1,N+1)]
mom=gamma_moments(N+2)
for r in range(N+1):
    rhs=sum(C0[(i,)]*(B[j]*mom[k]/factorial(k)
                + (mom[k+2]/(2*factorial(k)) if j==0 else 0))
             for i in range(r+1) for j in range(r-i+1)
             for k in [r-i-j])
    check('one_log_generator',abel_polynomial(polys[(r,1)]).subs(L,0),rhs)
    if r>=1:
        explicit=(-1)**r*(-Z(r+1,1)+G*z(r+1)+s.Rational(r+1,2)*z(r+2)
             +s.Rational(1,2)*sum(z(j+1)*z(r-j+1) for j in range(1,r)))
        check('one_log_stieltjes_cancellation',specialize_a_one(rhs),explicit)

N=4; polys2=cutoff_polynomials((N,2));C0=exp_coefficients(cumulants((N,)),(N,))
B=[g(1)]+[(-1)**(j+1)*Z(j+1,1) for j in range(1,N+1)]
M=[(-1)**(j+1)*(j+1)*Z(j+2,2) for j in range(N+1)]
mom=gamma_moments(N+4)
for r in range(N+1):
    rhs=0
    for i in range(r+1):
        for j in range(r-i+1):
            k=r-i-j
            b2=sum(B[h]*B[j-h] for h in range(j+1))
            rhs+=C0[(i,)]*((b2+M[j])*mom[k]/(2*factorial(k))
                           +B[j]*mom[k+2]/(2*factorial(k))
                           +(mom[k+4]/(8*factorial(k)) if j==0 else 0))
    check('two_log_generator',abel_polynomial(polys2[(r,2)]).subs(L,0),rhs)

# Laurent coefficients; upper truncation chosen to retain each later constant.
t=s.Symbol('t')
eta=1/t+sum((-1)**j*g(j)*t**j/factorial(j) for j in range(5))
powers={1:eta}
for k in range(2,6):
    powers[k]=sum(k**j*Z(k,j)*t**j/factorial(j) for j in range(5))
E={0:s.Integer(1)}
for d in range(1,6):
    ex=sum((-1)**(k-1)*powers[k]*E[d-k] for k in range(1,d+1))/d
    E[d]=s.series(ex,t,0,6-d).removeO().expand()
    part=sum(mobius(p)*s.prod(powers[len(B)] for B in p)
             for p in partitions(tuple(range(d))))/factorial(d)
    ct=s.expand(part).coeff(t,0)
    check('diagonal_newton_vs_partitions',E[d].coeff(t,0),ct)
check('diagonal_depth_two',E[2].coeff(t,0),(g(0)**2-Z(2))/2-g(1))
check('diagonal_depth_three',E[3].coeff(t,0),(g(0)**3-3*g(0)*Z(2)+2*Z(3))/6-g(0)*g(1)+g(2)/4-Z(2,1))

N=7
loghalf={(1,):2*s.log(2)}
for k in range(2,N+1): loghalf[(k,)]=s.Rational((-1)**k*(2-2**k),k)*z(k)
half=exp_coefficients(loghalf,(N,))
for d in range(N+1):
    subs={g(0):G+2*s.log(2), **{Z(k):(2**k-1)*z(k) for k in range(2,N+1)}}
    check('half_shift_gamma_ratio',abel_polynomial(P0[(d,)]).subs(L,0).subs(subs),half[(d,)])
for M0 in range(1,7):
    inv=s.prod((1+u/s.Integer(j))**-1 for j in range(1,M0))
    inv=s.series(inv,u,0,6).removeO().expand()
    subs={g(0):G-s.harmonic(M0-1)}
    subs.update({Z(k):z(k)-s.harmonic(M0-1,k) for k in range(2,7)})
    for d in range(6):
        check('integer_shift_gamma_ratio',abel_polynomial(P0[(d,)]).subs(L,0).subs(subs),inv.coeff(u,d))

for M0 in range(1,6):
    for n in range(M0,10):
        left=s.prod(1+u/s.Integer(j) for j in range(M0,n))*u/s.Integer(n)
        right=s.rf(u,n)/factorial(n)/s.prod(1+u/s.Integer(j) for j in range(1,M0))
        check('primitive_finite_shift_deletion',s.cancel(left-right),0)

for q in range(2,13):
    for p in range(1,q+1):
        for k in range(1,3*q+1):
            x=s.Symbol('x')
            filt=sum(x**((j*(k-p))%q) for j in range(q))
            rem=s.rem(filt,s.cyclotomic_poly(q,x),x)
            check('root_of_unity_filter',rem,q if (k-p)%q==0 else 0)

# One arbitrary logarithmic decoration, including higher spectral derivatives.
for ell in range(2,5):
    N=4
    bound=(N,)+(0,)*(ell-1)+(1,)
    pp=cutoff_polynomials(bound)
    cc=exp_coefficients(cumulants((N,)),(N,))
    gm=gamma_moments(N+ell+1)
    bb=[g(ell)]+[(-1)**(j+ell)*Z(j+1,ell) for j in range(1,N+1)]
    for r in range(N+1):
        alpha=(r,)+(0,)*(ell-1)+(1,)
        rhs=sum(cc[(i,)]*(bb[j]*gm[k]/factorial(k)
                 +(gm[k+ell+1]/((ell+1)*factorial(k)) if j==0 else 0))
                for i in range(r+1) for j in range(r-i+1) for k in [r-i-j])
        check('one_higher_decoration_generator',abel_polynomial(pp[alpha]).subs(L,0),rhs)
        if r:
            check('positive_index_stieltjes_cancellation',
                  s.diff(specialize_a_one(rhs),g(ell)),0)

# Noncommutative Gamma-conjugated differentiation recurrence.
bound=(2,1,1)
pp=cutoff_polynomials(bound)
qq={a:abel_polynomial(v) for a,v in pp.items()}
def T(poly):
    if poly==0:return s.Integer(0)
    deg=int(s.degree(poly,L))
    return s.expand((L-G)*poly+sum((-1)**(k+1)*z(k+1)*s.diff(poly,L,k)
                                   for k in range(1,deg+1)))
for a in indices(bound)[1:]:
    rhs=0
    for r,count in enumerate(a):
        if count:
            b=list(a);b[r]-=1;b=tuple(b)
            v=qq[b]
            for j in range(r):v=T(v)
            rhs+=v
    check('gamma_conjugated_differentiation',s.diff(qq[a],L),rhs)

# Integer-shift elementary endpoint expression and finite harmonic identity.
for M0 in range(2,9):
    for d in range(1,8):
        elementary=s.Rational(1,factorial(d))*L**d
        # Endpoint polynomial: exponential terms are dropped, not evaluated at L=0.
        for j in range(1,M0):
            elementary-=(-1)**j*s.binomial(M0-1,j)*s.Rational(1,(-j)**d)*sum((-j*L)**k/factorial(k) for k in range(d))
        invc=[s.Integer(1)]+[s.Integer(0)]*d
        for j in range(1,M0):
            invc=[sum(invc[n-k]*s.Rational((-1)**k,j**k) for k in range(n+1)) for n in range(d+1)]
        gamma_poly=sum(invc[d-k]*L**k/factorial(k) for k in range(d+1))
        check('integer_elementary_endpoint',elementary,gamma_poly)

catalog={}
for content in [(1,0),(0,1),(2,0),(1,1),(2,1),(3,1),(0,2),(1,2),(0,0,1),(1,0,1)]:
    pp=cutoff_polynomials(content)[content]
    qq=abel_polynomial(pp)
    catalog[str(content)]={'cutoff_polynomial':str(pp),'abel_polynomial':str(qq),
                          'a_one_abel_polynomial':str(specialize_a_one(qq)),
                          'a_one_endpoint_latex':s.latex(specialize_a_one(qq.subs(L,0)))}
(ROOT/'results/coefficient_catalog.json').write_text(json.dumps(catalog,indent=2)+'\n')
out={'status':'PASS','exact_assertions':sum(counts.values()),'groups':counts,
     'python':platform.python_version(),'sympy':s.__version__,
     'meaning':'Finite polynomial and rational checks; analytic proofs are in the article.'}
(ROOT/'results/exact_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
