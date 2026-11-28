#!/usr/bin/env python3
"""Exact finite regressions for the paper; not a proof or Lean replay."""
from math import gcd, lcm
from collections import Counter
import sympy as S
from sympy import Poly, Matrix, cyclotomic_poly, legendre_symbol, totient
x = S.Symbol('x')

def units(n):
    return [a for a in range(n) if gcd(a,n)==1]

def split_part(n,p):
    a=0
    while n%p==0:
        n//=p; a+=1
    return n,a

def chi(d,p):
    return int(legendre_symbol(p,d))

def orbit(z,b,m,p,c):
    out=[]; t=(z,b)
    while t not in out:
        out.append(t)
        t=(t[0]*p%m, t[1]^(c==-1))
    assert t==out[0]
    return out

def poly_degrees(f,p):
    return Counter((g.degree(), a) for g,a in Poly(f,x,modulus=p).factor_list()[1])

def finite_case(n,d,p):
    m,a=split_part(n,p); c=chi(d,p)
    ep=1 if a==0 else (p-1)*p**(a-1)
    eb=2 if p==d else 1
    bits=range(1 if p==d else 2)
    # Independent polynomial factorization of the two components.
    fc=Poly(cyclotomic_poly(n,x),x,modulus=p).factor_list()[1]
    fq=Poly(x*x-x+(d+1)//4,x,modulus=p).factor_list()[1]
    assert all(e==ep for _,e in fc)
    assert all(e==eb for _,e in fq)
    degs=Counter()
    for g,e in fc:
        for h,f in fq:
            degs[(lcm(g.degree(),h.degree()),e*f)]+=gcd(g.degree(),h.degree())
    pts={(z,b) for z in units(m) for b in bits}; orbits=[]
    while pts:
        O=set(orbit(*min(pts),m,p,c)); assert O<=pts
        pts-=O; orbits.append(O)
    assert degs==Counter((len(O),ep*eb) for O in orbits)
    assert sum(k*e*v for (k,e),v in degs.items())==2*int(totient(n))
    # Every pullback comparison, including bad primes and p=d.
    z=1%m; O0=orbit(z,0,m,p,c); f=len(O0)
    assert all(len(O)==f for O in orbits)
    for v in units(n):
        for e in (1,-1):
            other=(e%m,0 if p==d else int(e==-1))
            lhs=(v%m,0) in set(orbit(*other,m,p,c))
            rhs=any(v%m==e*pow(p,j,m)%m and (p==d or e==c**j) for j in range(f))
            assert lhs==rhs
    return len(orbits), 2*len(units(n))

def multiplication_matrix(g,f):
    h=f.degree(); return Matrix.hstack(*[Matrix([S.rem(g*x**j,f.as_expr(),x).coeff(x,i) for i in range(h)]) for j in range(h)])

def dual_check(f):
    h=f.degree(); expr=f.as_expr()
    traces=[S.trace(multiplication_matrix(x**i,f)) for i in range(2*h-1)]
    T=Matrix(h,h,lambda i,j:traces[i+j]); D=T.det()
    invder=S.invert(f.diff().as_expr(),expr,x)
    U=T*multiplication_matrix(invder,f)
    assert all(v.q==1 for v in U) and abs(U.det())==1
    assert D==S.discriminant(expr,x)
    return T,U,D

def phase_check(n):
    f=Poly(cyclotomic_poly(n,x),x,domain='QQ'); h=f.degree()
    R=lambda g:S.rem(g,f.as_expr(),x)
    star=lambda g:R(sum(c*x**((-i[0])%n) for i,c in Poly(g,x).terms()))
    u=R(x**((n//4+1-h//2)%n)); dp=f.diff().as_expr()
    assert R(star(dp)+x**((2-h)%n)*dp)==0
    assert R(star(u)*u-1)==0
    assert star(R(u*dp))==R(u*dp)
    assert R(x**n-1)==0

cases=orbs=tests=0
for n in (4,8,12,16,20,24,28,36,40,48,60):
    for d in (7,11,19,23,31):
        if gcd(n,d)>1: continue
        for p in (2,3,5,7,11,13,17,19,23,31):
            g,t=finite_case(n,d,p); cases+=1; orbs+=g; tests+=t
print(f'Finite quotient: {cases} (n,d,p) cases; {orbs} geometric orbits; {tests} pullback comparisons.')
for n in (4,8,12,16,20,24,28,36,40,48,60,84,96): phase_check(n)
print('Reciprocal-derivative phase: 13 exact cyclotomic quotient rings.')
count=0
for n in (4,8,12,16,20,24,28):
    B=Poly(cyclotomic_poly(n,x),x,domain='QQ'); TB,UB,DB=dual_check(B)
    for d in (7,11,19):
        if gcd(n,d)>1: continue
        A=Poly(x*x-x+(d+1)//4,x,domain='QQ'); TA,UA,DA=dual_check(A)
        assert gcd(abs(int(DA)),abs(int(DB)))==1
        # Tensor dual certificate: multiplication by inverse product has unimodular pairing.
        # Kronecker determinant follows from determinants of factors; verify matrix identity.
        T=S.kronecker_product(TA,TB); U=S.kronecker_product(UA,UB)
        assert T.shape==U.shape and all(v.q==1 for v in U)
        assert all(v.q==1 for v in U.inv())
        count+=1
print(f'Trace/codifferent: {count} exact tensor-basis unimodularity checks.')
# Actual source parameter class, at s=0,2,4 (not a claim of full admissible data).
q0,d=18480,9239; assert S.isprime(d) and d%q0==q0//2-1
large=0
for s in (0,2,4):
    n=q0*3**(int(S.integer_log(s,3)[0] if s else 0)+5)*2**s
    for p in (2,3,5,7,11,13,17,19,23,31,37,41,d):
        m,a=split_part(n,p); c=chi(d,p)
        # use sets, not list membership, for these bigger orbits
        z=1%m; b=0; seen=set()
        while (z,b) not in seen:
            seen.add((z,b)); z=z*p%m; b^=(c==-1)
        assert (z,b)==(1%m,0)
        f=len(seen); assert f==lcm(int(S.n_order(p,m)) if m>1 else 1,2 if c==-1 else 1)
        fixed=((-1)%m,0 if p==d else 1) in seen
        if fixed: assert p%(2**(s+1))==(-1)%(2**(s+1))
        if p==d or n%p==0: assert not fixed
        large+=1
print(f'Source-congruence examples: {large} prime/tower cases for q0=18480, d=9239.')
print('All exact checks passed.')
