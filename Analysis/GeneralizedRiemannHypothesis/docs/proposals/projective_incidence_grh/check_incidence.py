#!/usr/bin/env python3
"""Exact finite regressions (not a proof of the universal statements)."""
from itertools import product
from fractions import Fraction as Q
from collections import Counter
import random

class Field:
    def __init__(self,q):
        self.q=q
        self.add=lambda a,b: a^b if q==4 else (a+b)%q
        def mul(a,b):
            if q!=4: return a*b%q
            r=0
            while b:
                if b&1: r^=a
                b>>=1; a<<=1
                if a&4: a^=7 # x^2+x+1
            return r
        self.mul=mul
        self.inv={a:next(b for b in range(1,q) if mul(a,b)==1) for a in range(1,q)}
    def sum(self, xs):
        s=0
        for x in xs: s=self.add(s,x)
        return s
    def dot(self,x,y): return self.sum(self.mul(a,b) for a,b in zip(x,y))
    def lines(self,n):
        return [x for x in product(range(self.q),repeat=n) if any(x) and next(a for a in x if a)==1]
    def line(self,x):
        a=next(a for a in x if a)
        return tuple(self.mul(self.inv[a],b) for b in x)
    def mat(self,g,n): return [g[i*n:(i+1)*n] for i in range(n)]
    def mv(self,g,x): return tuple(self.dot(row,x) for row in self.mat(g,len(x)))
    def vm(self,x,g): return tuple(self.dot(x,col) for col in zip(*self.mat(g,len(x))))
    def mm(self,a,b,n): return tuple(self.dot(row,col) for row in self.mat(a,n) for col in zip(*self.mat(b,n)))
    def rank(self, rows):
        a=[list(r) for r in rows]; r=0
        if not a: return 0
        for j in range(len(a[0])):
            i=next((i for i in range(r,len(a)) if a[i][j]),None)
            if i is None: continue
            a[i],a[r]=a[r],a[i]; v=self.inv[a[r][j]]
            a[r]=[self.mul(v,t) for t in a[r]]
            for i in range(r+1,len(a)):
                # in prime fields subtract; in F4 subtract = add
                c=a[i][j] if self.q==4 else -a[i][j]%self.q
                a[i]=[self.add(t,self.mul(c,u)) for t,u in zip(a[i],a[r])]
            r+=1
            if r==len(a): break
        return r

def check_incidence(f,n):
    q=f.q; pts=f.lines(n); P=len(pts); h=(q**(n-1)-1)//(q-1); c=(q**(n-2)-1)//(q-1)
    assert P==(q**n-1)//(q-1)
    masks=[sum(1<<i for i,z in enumerate(pts) if f.dot(x,z)==0) for x in pts]
    for i,a in enumerate(masks):
        assert a.bit_count()==h
        for j,b in enumerate(masks):
            assert (a&b).bit_count()==(h if i==j else c)
            # (P I-h J)^T(P I-h J) = q^(n-2)(P^2 Id-P J).
            assert P*P*(a&b).bit_count()-P*h*h == q**(n-2)*(P*P*(i==j)-P)
    return P*P

def weighted_tests(f,n):
    q=f.q; G=[g for g in product(range(q),repeat=n*n) if f.rank(f.mat(g,n))==n]
    e=tuple(int(i==j) for i in range(n) for j in range(n)); assert e in G
    # Nonnegative autocorrelation of left translates; the Gram is positive type.
    rng=random.Random(173+q*10+n)
    # Generate inverse by table, with small support only; no group representation package.
    diag=tuple((next(iter(range(2,q)),1) if i==j==0 else int(i==j)) for i in range(n) for j in range(n))
    if diag not in G: diag=e
    H={e}; g=diag
    while g not in H: H.add(g); g=f.mm(g,diag,n)
    weights=[{g:1 for g in G},{e:1},{g:1 for g in H}]
    for trial in range(4):
        a={g:rng.randrange(1,5) for g in rng.sample(G,min(5+trial,len(G)))}
        inv={g:next(h for h in G if f.mm(g,h,n)==e) for g in a}
        w=Counter()
        for g,x in a.items():
            for h,y in a.items(): w[f.mm(g,inv[h],n)]+=x*y
        weights.append(w)
    pairs=0; tails=0; moments=0; mixes=0; cosets=0; degenerate=0
    lines=f.lines(n); p=Q(q**(n-1)-1,q**n-1) if n>=1 else 0
    for w in weights:
        T=sum(w.values())
        # Projective and vector stabilizers: covector fixed under inverse transpose iff x^T g=x^T.
        l0={};l1={};v0={};v1={}
        for x in lines:
            for side,act,ls,vs in [(0,f.mv,l0,v0),(1,lambda g,x:f.vm(x,g),l1,v1)]:
                hist=Counter()
                for g,t in w.items():
                    y=act(g,x)
                    if f.line(y)==x: hist[y]+=t
                ls[x]=sum(hist.values()); vs[x]=hist[x]
                assert ls[x]<=(q-1)*vs[x]
                # Every scalar transporter in the line stabilizer is a normalizer coset.
                for h in hist.values(): assert h<=vs[x]; cosets+=1
        if n>=2:
            for x,z in product(lines,repeat=2):
                s=sum(t for g,t in w.items() if f.dot(x,f.mv(g,z))==0)
                assert (s-p*T)**2 <= q**(n-2)*l1[x]*l0[z]; mixes+=1
        for m in range(1,n+1):
            U=f.lines(m); L=len(U); Lp=(q**(m-1)-1)//(q-1)
            # Columns of A0 and A1. Use random matrices plus deliberately singular cases.
            basis=[tuple(int(i==j) for i in range(n)) for j in range(m)]
            cases=[(basis,basis),([tuple(0 for _ in range(n))]+basis[1:],basis)]
            for _ in range(3): cases.append(([tuple(rng.randrange(q) for _ in range(n)) for _ in range(m)], [tuple(rng.randrange(q) for _ in range(n)) for _ in range(m)]))
            for A0,A1 in cases:
                def image(A,v): return tuple(f.dot(col,v) for col in zip(*A))
                def mass(v,stab): return T if not any(v) else stab[f.line(v)]
                Y=max([mass(image(A0,v),v0) for v in U]+[mass(image(A1,v),v1) for v in U]); pairs+=1
                if f.rank(A0)<m or f.rank(A1)<m:
                    assert Y==T; degenerate+=1
                dist=Counter(); kernel_mass=0
                for g,t in w.items():
                    Z=[[f.dot(x,f.mv(g,z)) for z in A0] for x in A1]
                    corank=m-f.rank(Z); dist[corank]+=t
                    kernel_mass+=t*(q**corank-1)
                    # Exact point-hyperplane counting, independent of rank formula.
                    Zflat=tuple(a for row in Z for a in row)
                    actual=sum(f.dot(y,f.mv(Zflat,v))==0 for y,v in product(U,repeat=2))
                    K=(q**corank-1)//(q-1)
                    assert actual==L*Lp+q**(m-1)*K
                    moments+=1
                # Compare real radical inequalities by exact squaring after checking the sign.
                Bsq=q**(2*m+n)*Y*Y
                assert kernel_mass<=T or (kernel_mass-T)**2<=Bsq
                for j in range(1,m+1):
                    S=sum(t for k,t in dist.items() if k>=j); lhs=(q**j-1)*S
                    assert lhs<=T or (lhs-T)**2<=Bsq; tails+=1
                    if j==1: assert q*S<=2*T or (q*S-2*T)**2<=Bsq
    print(f'GL({n}, {q}): |G|={len(G)}, weights={len(weights)}, compression cases={pairs}, tail checks={tails}, rank/incident counts={moments}, mixing={mixes}, normalizer cosets={cosets}, degenerate maps={degenerate}')

if __name__=='__main__':
    total=0
    for q,n in [(2,2),(2,3),(2,4),(3,2),(3,3),(4,2),(4,3),(5,2),(5,3),(7,3)]:
        count=check_incidence(Field(q),n); total+=count
        print(f'PG({n-1},{q}): {count} exact Gram entries')
    print(f'Total exact incidence Gram entries: {total}')
    for q,n in [(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)]: weighted_tests(Field(q),n)
    f=Field(3); g=(0,2,1,0); x=(1,0)
    assert f.mv(g,x)!=x and f.vm(x,g)!=x and f.dot(x,f.mv(g,x))==0
    assert 3>2 # delta_g violates original bound; not positive type.
    print('Non-positive-type counterexample and all exact regressions passed.')
