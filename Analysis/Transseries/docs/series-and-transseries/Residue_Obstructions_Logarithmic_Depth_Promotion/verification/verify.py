#!/usr/bin/env python3
"""Exact finite checks for the accompanying Hahn-transseries article.

This is not a proof of the infinite-support theorems. All symbolic tests use
rational arithmetic; mpmath values at the end are numerical illustrations.
Run: python verification/verify.py
Dependencies: sympy, mpmath.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import factorial, comb
import random
import json
from pathlib import Path
import sympy as sp
import mpmath as mp

# A block is a finite sum of rational multiples of L**b * T**c,
# where T = log L. Work with guard terms below the tested cutoff.
Block = dict[tuple[int, int], F]
CUTOFF = -28

def clean(p: Block) -> Block:
    return {m: F(c) for m, c in p.items() if c and m[0] >= CUTOFF}

def add(p: Block, q: Block, scale: F = F(1)) -> Block:
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, F(0)) + scale*c
    return clean(r)

def scale(p: Block, c: F) -> Block:
    return clean({m: c*v for m, v in p.items()})

def shift(p: Block, b: int) -> Block:
    return clean({(i+b, j): c for (i,j), c in p.items()})

def deriv(p: Block) -> Block:
    q: Block = {}
    for (b,c), a in p.items():
        if b:
            q[(b-1,c)] = q.get((b-1,c), F(0)) + a*b
        if c:
            q[(b-1,c-1)] = q.get((b-1,c-1), F(0)) + a*c
    return clean(q)

def primitive(p: Block) -> Block:
    q: Block = {}
    for (b,c), a in p.items():
        if b == -1:
            q = add(q, {(0,c+1): a/F(c+1)})
        else:
            for j in range(c+1):
                v = a * (-1)**j * F(factorial(c), factorial(c-j)) / F(b+1)**(j+1)
                q = add(q, {(b+1,c-j): v})
    return clean(q)

def shift_polynomial(roots: list[int], alpha: int) -> list[F]:
    p = [F(1)]
    for r in roots:
        q = [F(0)]*(len(p)+1)
        for j,a in enumerate(p):
            q[j] += a*(alpha-r)
            q[j+1] += a
        p=q
    return p

def apply_polynomial(p: list[F], f: Block) -> Block:
    g: Block = {}
    d = f
    for a in p:
        g=add(g,d,a)
        d=deriv(d)
    return g

def inverse_block(roots: list[int], alpha: int, f: Block) -> Block:
    """A truncated right inverse of P(alpha + d/dL), allowing log L."""
    p=shift_polynomial(roots, alpha)
    multiplicity=0
    while p[multiplicity] == 0:
        multiplicity += 1
    q=p[multiplicity:]
    h=f
    for _ in range(multiplicity):
        h=primitive(h)
    # Expand 1/Q(z), evaluating powers of d/dL. Differentiation decreases b.
    coeff: list[F]=[]
    ans: Block={}
    d=h
    k=0
    while d:
        if k==0:
            ak=1/q[0]
        else:
            ak=-sum(q[j]*coeff[k-j] for j in range(1,min(k,len(q)-1)+1))/q[0]
        coeff.append(ak)
        ans=add(ans,d,ak)
        d=deriv(d)
        k+=1
        if k>250:
            raise RuntimeError('Unexpected derivative truncation failure')
    return ans

def visible(p: Block, min_b: int = -10) -> Block:
    return {m:c for m,c in p.items() if m[0]>=min_b and c}

def top_coefficient(s: int, k: int) -> F:
    roots=list(range(s))
    c=F(1)
    for h in range(1,k+1):
        j=s-1-h
        pp=F(1)
        for r in roots:
            if r!=j:
                pp*=j-r
        c=-c/(h*pp)
    return c

def check_blocks() -> dict:
    checks=0
    # Exact primitives, including resonant log terms.
    for b in range(-5,6):
        for c in range(5):
            p={(b,c):F(1)}
            assert deriv(primitive(p))==p
            checks+=1
    rows=[]
    for s in range(1,7):
        roots=list(range(s))
        blocks={s-1:{(0,0):F(1)}}
        for alpha in range(s-2,-4,-1):
            f=scale(shift(blocks[alpha+1],-1),F(-1))
            blocks[alpha]=inverse_block(roots,alpha,f)
            residual=add(apply_polynomial(shift_polynomial(roots,alpha),blocks[alpha]),
                         shift(blocks[alpha+1],-1))
            assert not visible(residual), (s,alpha,visible(residual))
            checks+=1
        for k in range(s):
            alpha=s-1-k
            assert max((c for (b,c) in blocks[alpha]),default=0)==k
            assert blocks[alpha].get((0,k),F(0))==top_coefficient(s,k)
            checks+=2
        rows.append({'s':s,'homogeneous_T_degree':s-1,
                     'coefficient_at_x0':str(top_coefficient(s,s-1))})
        # Forcing x^(s-1)/L: sharp degree s at the last resonance.
        forced={s-1:inverse_block(roots,s-1,{(-1,0):F(1)})}
        for alpha in range(s-2,-1,-1):
            forced[alpha]=inverse_block(roots,alpha,scale(shift(forced[alpha+1],-1),F(-1)))
        expected=F((-1)**(s-1+s*(s-1)//2),
                   factorial(s)*__import__('math').prod(factorial(j) for j in range(s))**2)
        assert forced[0][(0,s)]==expected
        assert max(c for b,c in forced[0])==s
        checks+=2
    # Repeated-root examples, checked above the guard band.
    for m in range(1,6):
        for b in range(-m-1,3):
            f={(b,0):F(1)}
            g=inverse_block([2]*m,2,f)
            assert not visible(add(apply_polynomial(shift_polynomial([2]*m,2),g),f,F(-1)))
            assert max((c for b,c in g),default=0)<=1
            checks+=2
    return {'exact_block_checks':checks,'sharpness':rows}

def check_finite_reduction() -> dict:
    rng=random.Random(20260929)
    cases=0
    for n in range(1,7):
        for trial in range(4):
            size=2*n
            P=sp.zeros(size); G=sp.zeros(size)
            K=sp.zeros(size,n); Pi=sp.zeros(n,size)
            for i in range(n):
                P[2*i+1,2*i+1]=1; G[2*i+1,2*i+1]=1
                K[2*i,i]=1; Pi[i,2*i]=1
            R=sp.zeros(size)
            for target in range(n):
                for source in range(target):
                    for i in range(2):
                        for j in range(2):
                            R[2*target+i,2*source+j]=rng.randrange(-2,3)
            I=sp.eye(size)
            N=sp.zeros(size); power=I
            for _ in range(n):
                N+=power; power=-G*R*power
            assert power==sp.zeros(size)
            assert (I+G*R)*N==I
            M=Pi*R*N*K
            B=Pi-Pi*R*N*G
            Lop=P+R
            assert B*Lop==M*Pi
            assert size-Lop.rank()==n-M.rank()
            assert B*K==sp.eye(n)
            u=sp.Matrix([rng.randrange(-4,5) for _ in range(size)])
            f=Lop*u
            c=Pi*u
            assert M*c==B*f
            assert N*(K*c+G*f)==u
            cases+=1
    return {'exact_finite_matrix_cases':cases,'seed':20260929}

def numerical_illustrations() -> list[dict]:
    mp.mp.dps=70
    rows=[]
    for x0 in [10,100,10000]:
        x=mp.mpf(x0); L=mp.log(x); T=mp.log(L)
        S=mp.exp(L)*mp.e1(L)
        N=int(mp.floor(L))
        partial=mp.fsum([(-1)**k*mp.factorial(k)/L**(k+1) for k in range(N)])
        rem=(-1)**N*(S-partial)
        assert 0<rem<mp.factorial(N)/L**(N+1)
        eta=1/(2*x*L)
        bound=(T/(2*x*L)+mp.mpf(5)/(4*x*L**2))/(1-eta)
        rows.append({'x':x0,'L':mp.nstr(L,18),'S':mp.nstr(S,18),
                     'z':mp.nstr(x+T+S,18),'analytic_error_bound':mp.nstr(bound,12),
                     'terms_N':N,'signed_Borel_remainder':mp.nstr(rem,12)})
    return rows

def main() -> None:
    result={'status':'all checks passed','scope':'finite exact checks, not formal theorem verification'}
    result.update(check_blocks())
    result.update(check_finite_reduction())
    result['numerical_illustrations']=numerical_illustrations()
    output=json.dumps(result,indent=2)
    print(output)
    Path(__file__).with_name('results.json').write_text(output+'\n')

if __name__=='__main__':
    main()
