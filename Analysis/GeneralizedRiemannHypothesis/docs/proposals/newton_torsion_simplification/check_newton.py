#!/usr/bin/env python3
"""Exact finite regressions for the Newton torsion selection note.
No external dependencies. Not a proof of the uniform theorem.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
from random import Random


def vp(n, p):
    if not n:
        return float('inf')
    n = abs(n)
    s = 0
    while n % p == 0:
        n //= p
        s += 1
    return s


def exponents(p, j):
    return [k for k in range(1, p**j) if k % p]


def check_denominators():
    cases = 0
    for p, jmax in [(2,9),(3,6),(5,4),(7,3),(11,2)]:
        for j in range(1,jmax+1):
            es = exponents(p,j)
            # Exhaust small prefixes, sample the larger ones deterministically.
            ks = sorted(set(range(min(len(es), 33))) | {len(es)//2,len(es)-1})
            for k in ks:
                for i in (range(k+1) if k <=32 else {0,k//2,k}):
                    den = sum(p**vp(es[i]-es[h],p) for h in range(k+1) if h != i)
                    # The valuation is den / phi(p^j).
                    assert den <= k + 2*k*(j-1)*F(p-1,p)
                    assert den <= 2*j*k
                    assert es[k]-es[0] <= 2*k
                    cases += 1
    print(f'Primitive-node denominator inequalities: {cases} exact checks')


class Cyclotomic:
    """Z[pi], pi=zeta_(p^j)-1, in the Eisenstein power basis."""
    def __init__(self,p,j):
        self.p,self.j=p,j
        self.K=(p-1)*p**(j-1)
        self.t=F(1,self.K)
        # Phi_{p^j}(1+X) = sum_{a=0}^{p-1} (1+X)^(a*p^(j-1)).
        self.mod=[0]*(self.K+1)
        for a in range(p):
            d=a*p**(j-1)
            for k in range(d+1): self.mod[k]+=comb(d,k)
        assert self.mod[-1]==1 and self.mod[0]==p
        assert all(c%p==0 for c in self.mod[:-1])
        self.zero=self.const(0); self.one=self.const(1)
        self.pi=self.reduce([0,1]); self.zeta=self.add(self.one,self.pi)
        self.nodes=[self.sub(self.pow(self.zeta,e),self.one) for e in exponents(p,j)]
        assert all(self.val(a)==self.t for a in self.nodes)
        assert len(set(self.nodes))==self.K
        assert self.pow(self.zeta,p**j)==self.one
        assert self.pow(self.zeta,p**(j-1))!=self.one

    def reduce(self,cs):
        cs=list(cs)+[0]*max(0,self.K-len(cs))
        for k in range(len(cs)-1,self.K-1,-1):
            a=cs[k]
            for r in range(self.K): cs[k-self.K+r]-=a*self.mod[r]
        return tuple(cs[:self.K])
    def const(self,n): return (n,)+(0,)*(self.K-1)
    def add(self,a,b): return tuple(x+y for x,y in zip(a,b))
    def neg(self,a): return tuple(-x for x in a)
    def sub(self,a,b): return self.add(a,self.neg(b))
    def mul(self,a,b):
        c=[0]*(2*self.K-1)
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b):
                    if y: c[i+j]+=x*y
        return self.reduce(c)
    def pow(self,a,k):
        y=self.one
        while k:
            if k&1: y=self.mul(y,a)
            a=self.mul(a,a); k//=2
        return y
    def val(self,a):
        # Distinct fractional parts ensure no cancellation among basis terms.
        return min((F(vp(x,self.p))+F(i,self.K) for i,x in enumerate(a) if x),default=float('inf'))
    def sum(self,items):
        s=self.zero
        for a in items: s=self.add(s,a)
        return s
    def prod(self,items):
        s=self.one
        for a in items: s=self.mul(s,a)
        return s
    def node(self,k): return self.nodes[k] if k<self.K else self.nodes[0]

    def monomial_newton(self,d):
        # X*N_k = N_{k+1} + a_k*N_k.
        c=[self.one]
        for _ in range(d):
            y=[self.zero]*(len(c)+1)
            for k,x in enumerate(c):
                y[k+1]=self.add(y[k+1],x)
                y[k]=self.add(y[k],self.mul(x,self.node(k)))
            c=y
        for k,x in enumerate(c): assert self.val(x)>=(d-k)*self.t
        return c

    def newton(self,P):
        C={}
        for nu,a in P.items():
            factors=[self.monomial_newton(d) for d in nu]
            for alpha in product(*(range(d+1) for d in nu)):
                c=self.prod([a]+[f[k] for f,k in zip(factors,alpha)])
                C[alpha]=self.add(C.get(alpha,self.zero),c)
        return {alpha:c for alpha,c in C.items() if c!=self.zero}
    def eval(self,P,x):
        return self.sum(self.prod([a]+[self.pow(y,d) for y,d in zip(x,nu)]) for nu,a in P.items())
    def gauss(self,P,t):
        return min(self.val(a)+sum(nu)*t for nu,a in P.items())
    def eval_newton(self,C,x):
        return self.sum(self.prod([a]+[self.sub(y,self.node(k)) for y,d in zip(x,alpha) for k in range(d)]) for alpha,a in C.items())
    def divdiff_identity(self,P,C,alpha):
        # Tensor Lagrange leading coefficient functional, clearing all denominators.
        ix=list(product(*(range(k+1) for k in alpha)))
        vals=[]; dens=[]
        for ii in ix:
            x=tuple(self.node(i) for i in ii)
            vals.append(self.eval(P,x))
            d=self.prod(self.sub(self.node(i),self.node(h)) for i,k in zip(ii,alpha) for h in range(k+1) if h!=i)
            assert d!=self.zero
            assert self.val(d)<=2*self.j*sum(alpha)*self.t
            dens.append(d)
        allD=self.prod(dens)
        left=self.mul(C[alpha],allD)
        right=self.sum(self.mul(y,self.prod(dens[:i]+dens[i+1:])) for i,y in enumerate(vals))
        assert left==right
        assert min(map(self.val,vals))<=self.val(C[alpha])+max(map(self.val,dens))
        return min(map(self.val,vals))


def check_newton():
    rng=Random(20261127)
    examples=valid=excess=0
    for p,j in [(2,2),(2,3),(3,2),(5,1)]:
        A=Cyclotomic(p,j)
        es=exponents(p,j)
        for i,h in product(range(A.K),repeat=2):
            if i!=h: assert A.val(A.sub(A.nodes[i],A.nodes[h]))==A.t*p**vp(es[i]-es[h],p)
        for dim in (1,2,3):
            for case in range(18):
                P={}
                for _ in range(6):
                    nu=tuple(rng.randrange(0,4) for _ in range(dim))
                    # Include non-rational integral coefficients as well as integers.
                    a=A.mul(A.const(rng.choice([-3,-2,-1,1,2,3])),A.pow(A.pi,rng.randrange(0,4)))
                    P[nu]=A.add(P.get(nu,A.zero),a)
                P={nu:a for nu,a in P.items() if a!=A.zero}
                if not P: continue
                C=A.newton(P)
                w=A.gauss(P,A.t)
                assert A.gauss(C,A.t)==w
                delta=w-A.gauss(P,A.t/p)
                minimizers=[nu for nu,a in P.items() if A.val(a)+sum(nu)*A.t==w]
                for alpha,c in C.items():
                    if A.val(c)+sum(alpha)*A.t==w:
                        assert any(all(k<=d for k,d in zip(alpha,nu)) for nu in minimizers)
                        assert (1-F(1,p))*sum(alpha)*A.t<=delta
                x=tuple(rng.choice(A.nodes) for _ in range(dim))
                assert A.eval(P,x)==A.eval_newton(C,x)
                examples+=1
                # Test the theorem on all cases for which a minimal index fits the grid.
                for alpha,c in C.items():
                    if A.val(c)+sum(alpha)*A.t==w and max(alpha)<A.K:
                        best=A.divdiff_identity(P,C,alpha)
                        assert best<=w+2*j*delta/(1-F(1,p))
                        valid+=1
                        if best>w: excess+=1
                        break
        # Adversary at a fixed order: Phi_{p^j}(1+X) vanishes on all primitive nodes.
        P={(i,):A.const(c) for i,c in enumerate(A.mod) if c}
        assert all(A.eval(P,(a,))==A.zero for a in A.nodes)
        assert A.gauss(P,A.t)==1
        assert A.gauss(P,A.t/p)==F(1,p)
    print(f'Newton basis / Gauss / evaluation identities: {examples} generated polynomials')
    print(f'Exact tensor divided differences and evaluation bounds: {valid} cases ({excess} with nonzero excess)')
    print('Fixed-order obstruction: all 4 cyclotomic examples verified')


def check_harmonic():
    # Purely rational simulation of Gauss drops, including arbitrary large degrees.
    rng=Random(13)
    checked=0
    for p in (2,3,5):
        for _ in range(50):
            # Random sum of weighted Gauss minima for products of linear/monomial tests.
            polys=[[(F(rng.randrange(0,15),10),rng.randrange(0,2**rng.randrange(1,20))) for k in range(5)] for i in range(3)]
            d0=rng.randrange(1,5); H=d0+70
            t=lambda j:F(1,(p-1)*p**(j-1))
            w=lambda j:sum(min(v+d*t(j) for v,d in P) for P in polys)
            B=w(d0)
            ds=[w(j)-w(j+1) for j in range(d0,H+1)]
            assert min(ds)>=0 and sum(ds)==B-w(H+1)<=B
            harmonic=sum(F(1,j) for j in range(d0,H+1))
            assert min(j*d for j,d in zip(range(d0,H+1),ds))*harmonic<=B
            checked+=1
    print(f'Harmonic telescoping and weighted pigeonhole: {checked} rational models')


if __name__=='__main__':
    check_denominators()
    check_newton()
    check_harmonic()
    print('All checks passed.')
