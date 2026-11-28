#!/usr/bin/env python3
"""Exact finite regression tests for the paper's bookkeeping (not a Lean proof)."""
from fractions import Fraction as F
from random import Random
from math import prod

rng = Random(27112026)

def det(a):
    n = len(a)
    a = [[F(x) for x in row] for row in a]
    d = F(1)
    for i in range(n):
        j = next((j for j in range(i, n) if a[j][i]), None)
        if j is None: return F(0)
        if i != j: a[i], a[j] = a[j], a[i]; d = -d
        q = a[i][i]; d *= q
        for j in range(i+1, n):
            t = a[j][i] / q
            for k in range(i+1, n): a[j][k] -= t*a[i][k]
            a[j][i] = 0
    return d

def tr(a): return [list(x) for x in zip(*a)]
def mul(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in tr(b)] for row in a]
def diag(xs): return [[x if i==j else F(0) for j in range(len(xs))] for i,x in enumerate(xs)]
def gram(a): return mul(tr(a),a)
def power(p,e): return F(p)**e

def val(a,p):
    a=F(a); assert a
    v=0; n=abs(a.numerator); d=a.denominator
    while n%p==0: n//=p; v+=1
    while d%p==0: d//=p; v-=1
    return v

def random_invertible(d):
    while True:
        a=[[F(rng.randint(-4,4)) for _ in range(d)] for _ in range(d)]
        if det(a): return a

# The two clearing matrices are different and their product is not assumed diagonal.
# Rational vectors model the case of equal conjugate embeddings; the paper covers general embeddings.
count=0
for p in [2,3,5,7]:
  for d in range(1,6):
    for n in range(d+1):
      for r in [-5,-2,0,1,4]:
        a=random_invertible(d)
        exps=[rng.randrange(4) for _ in range(n)]
        gam=power(p,rng.randrange(-3,4))
        w=mul(a,diag([power(p,-r-k) for k in exps]+[1/gam]*(d-n)))
        G=gram(w); D=det(G)
        cl=diag([power(p,r+k) for k in exps]+[gam]*(d-n))
        extra=[rng.randrange(3) for _ in range(n)]
        cl2=diag([power(p,r+k+l) for k,l in zip(exps,extra)]+[gam]*(d-n))
        # Integral elementary column operation on the short block.
        if n>=2:
            cl[0][1]=cl[0][0]
        H=mul(mul(tr(cl2),G),cl)
        assert all(val(z,p)>=0 for row in H for z in row if z)
        assert det(H)==det(cl2)*D*det(cl)
        assert val(gam**(2*(d-n))*D,p)>=-2*sum(exps)-sum(extra)-2*n*r
        # Full-dimensional Gram ratio, with two different injective maps.
        t=random_invertible(d); s=random_invertible(d)
        D1=det(gram(mul(s,w))); Dxi=det(gram(mul(t,w)))
        assert D1*det(gram(t))==Dxi*det(gram(s))
        count+=1
print(f'local signed Gram bounds, cross-clearing and determinant ratios: {count} cases PASS')

# Product formula over rational norms, including extra primes in the credit support.
P=[2,3,5,7,11,13]; count=0
for _ in range(1000):
    vs=[rng.randint(-8,8) for _ in P]
    A=prod(power(p,v) for p,v in zip(P,vs))
    r=[rng.randrange(9) for _ in P]
    q=[max(0,rr-v)+rng.randrange(3) for rr,v in zip(r,vs)]
    assert all(-v<=qq-rr for v,qq,rr in zip(vs,q,r))
    assert abs(A)*prod(power(p,-v) for p,v in zip(P,vs))==1
    assert abs(A)*prod(power(p,qq-rr) for p,qq,rr in zip(P,q,r))>=1
    count+=1
print(f'signed product formula (rational exact multiplicative checks): {count} cases PASS')

# Gaussian conjugation warning: (2+i)/(2-i) has opposite valuations at the two primes.
def div_gauss(z,w):
    a,b=z; c,d=w; s=c*c+d*d
    return F(a*c+b*d,s),F(b*c-a*d,s)
def integral(z): return all(x.denominator==1 for x in z)
assert integral(div_gauss((2,1),(2,1)))
assert not integral(div_gauss((2,-1),(2,1)))
assert integral(div_gauss((2,-1),(2,-1)))
assert not integral(div_gauss((2,1),(2,-1)))
assert F(2*2+1,2*2+1)==1
print('Gaussian conjugate-valuation counterexample: PASS')

count=0
for _ in range(3000):
    p=rng.choice(P); f=rng.randint(1,20); a=rng.randint(p,5000); m=rng.randint(1,100)
    k=rng.randint(1,f); parts=[0]*k
    for _ in range(rng.randint(0,f)): parts[rng.randrange(k)]+=a
    J=(2*m*f*a+p-1)//p
    cost=m*sum(F(12*A,m*p)+F(J,m*m*f) for A in parts)
    assert cost<=F(14*f*a,p)+F(1,m)<=F(15*f*a,p)
    count+=1
print(f'marked local cost: {count} cases PASS')

count=0
for u in range(1,31):
    lam=u**6
    for s in range(1,31):
        x=s*s; m=2*s; f=3; b=10; a=x*b
        assert 15*f*a*u*(1+u)+30*m*m*f*b*lam<=150*f*a*lam
        count+=1
print(f'global harmonic budget scale arithmetic: {count} cases PASS')

for extra in [0,2]:
    lam=100
    # Extra 2b for the minimal implementation retaining the global scalar.
    def bound(B, inv_rank):
        return F(4,lam)+F(1+extra,lam**4)+inv_rank*(1+F(2,lam**4)+F(300*B*256,255*lam**2))
    old=bound(15,F(64,63)); new=bound(3,F(33,32))
    assert old<F(8,5) and new<F(6,5)
    print(f'constant bounds (extra rounding {extra}b): old {float(old):.9f}; adaptive {float(new):.9f} PASS')
print('ALL CHECKS PASSED. Finite arithmetic tests only; no Lean compilation performed.')
