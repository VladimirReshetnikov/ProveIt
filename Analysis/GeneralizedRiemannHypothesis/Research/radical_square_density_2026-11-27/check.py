#!/usr/bin/env python3
"""Exact finite regression tests for the square-start obstruction and packing.
No external packages. These tests are not a substitute for the general proof.
"""
from itertools import product
from fractions import Fraction
from functools import lru_cache

class Ring:
    def __init__(self, name, Q, add, mul, residue):
        self.name, self.Q, self.res = name, Q, residue
        self.A = range(Q)
        self.add = [[add(a,b) for b in self.A] for a in self.A]
        self.mul = [[mul(a,b) for b in self.A] for a in self.A]
        self.m = [a for a in self.A if not residue(a)]
        self.S = sorted({self.mul[a][a] for a in self.m})
        self.units = [a for a in self.A if residue(a)]
        self.root = {s: next(c for c in self.m if self.mul[c][c]==s) for s in self.S}
        assert all(self.add[a][a]==0 for a in self.m)
        assert all(self.mul[a][s]==0 for a in self.m for s in self.S)
        # Direct checks of ring identities for these tiny examples.
        for a,b,c in product(self.A,repeat=3):
            assert self.add[self.add[a][b]][c]==self.add[a][self.add[b][c]]
            assert self.mul[self.mul[a][b]][c]==self.mul[a][self.mul[b][c]]
            assert self.mul[a][self.add[b][c]]==self.add[self.mul[a][b]][self.mul[a][c]]
        assert all(self.add[a][0]==a and self.mul[a][1]==a for a in self.A)
        assert all(self.add[a][b]==self.add[b][a] and self.mul[a][b]==self.mul[b][a] for a,b in product(self.A,repeat=2))
    def trim(self,p):
        p=list(p)
        while p and p[-1]==0: p.pop()
        return tuple(p)
    def pmul(self,p,q):
        if not p or not q:return ()
        v=[0]*(len(p)+len(q)-1)
        for i,a in enumerate(p):
            if a:
                for j,b in enumerate(q):
                    if b: v[i+j]=self.add[v[i+j]][self.mul[a][b]]
        return self.trim(v)
    def padd(self,p,q):
        return self.trim([self.add[p[i] if i<len(p) else 0][q[i] if i<len(q) else 0] for i in range(max(len(p),len(q)))])
    def degree_res(self,f):
        return max((i for i,a in enumerate(f) if self.res(a)),default=-1)
    def obstruction(self,f,n):
        d=self.degree_res(f)
        if not 0<=d<=n-2:return False
        a,b=f[n],f[n-1]
        if (n-d)%2==0:
            return a in self.S and b== (a if d and self.res(f[d-1]) else 0)
        return a==0 and b in self.S
    def verify(self,n=3):
        Q=self.Q; S=self.S; B=Q**(n+1); w=Fraction(len(S),Q*Q)
        # All possible square polynomials for reduced degree e and residue start degree d.
        # If deg f + 2e > n, cancellation requires deg U <= n+2e-d;
        # if deg f + 2e <= n, the same bound is still necessary.
        @lru_cache(None)
        def squares(d,e):
            cap=n+2*e-d
            out=set()
            for low in product((0,1),repeat=e):
                t=low+(1,); t2=self.pmul(t,t)
                for us in product(S,repeat=cap//2+1):
                    U=[0]*(2*len(us)-1); U[::2]=us
                    out.add(self.padd(t2,U))
            return out
        dcount=eligible=0
        for f in product(self.A,repeat=n+1):
            ob=self.obstruction(f,n); dcount+=ob
            d=self.degree_res(f)
            if not 0<=d<=n-2:continue
            possible=any(len(self.pmul(z,f))<=n+1 for e in range(1,(n-d)//2+1) for z in squares(d,e))
            assert possible == ob,(self.name,f)
            if ob:
                # Construct an actual progression by the socle correction.
                even=(n-d)%2==0
                s=f[n] if even else f[n-1]  # residue lead is 1 in F2
                j=(n+(2 if even else 1)-d)//2
                r=[0]*(j+1); r[1]=1; r[j]=self.root[s]
                r=self.trim(r)
                z=self.pmul(self.pmul(r,r),f); y=self.pmul(r,f)
                assert len(z)<=n+1
                while len(y)>n+1:
                    a=y[-1]; shift=len(y)-1-d
                    assert all(self.mul[a][b]==0 for b in self.m)
                    correction=(0,)*shift+(a,)
                    r=self.padd(r,correction); y=self.pmul(r,f)
                assert self.pmul(self.pmul(r,r),f)==z
                assert [self.degree_res(t) for t in (f,y,z)]==[d,d+1,d+2]
            eligible+=possible
        expected=B*w*(1-Fraction(1,2**(n-1)))
        assert dcount==expected,(dcount,expected)
        # Exact packing for d=n-2 and unit constant coefficient.
        seen=set(); count=0
        for low in product(self.A,repeat=n-1):
            if not (self.res(low[0]) and self.res(low[-1])):continue
            for s in S:
                f=low+(self.mul[s][low[-2]],self.mul[s][low[-1]])
                c=self.root[s]; r=(c,1,c,s)
                y=self.pmul(r,f); z=self.pmul(self.pmul(r,r),f)
                f=self.trim(f)
                assert max(len(f),len(y),len(z))<=n+1
                assert [self.degree_res(t) for t in (f,y,z)]==[n-2,n-1,n]
                assert y and self.mul[y[0]][y[0]]==s
                assert (z[0] if z else 0)==s
                assert not (set((f,y,z)) & seen)
                seen.update((f,y,z)); count+=1
        assert count==B*w/4
        print(f'{self.name:23} Q={Q:2} |S|={len(S):2} n={n}  deletion={dcount}/{B}  square-starts={eligible}  disjoint triples={count}')

def poly2(a,b):
    c=0
    for j in range(3):
        if (b>>j)&1:c^=a<<j
    return c&7

def radical_ring(diagonal):
    # basis 1,x,y,z; x*y=z (alternating) OR x*x=z (diagonal).
    def mul(a,b):
        c=(b if a&1 else 0)^(a if b&1 else 0)^((a&1)*(b&1))
        if diagonal: e=((a>>1)&1)*((b>>1)&1)
        else:e=(((a>>1)&1)*((b>>2)&1))^(((a>>2)&1)*((b>>1)&1))
        return c^(e<<3)
    return Ring('diagonal rank 1' if diagonal else 'alternating rank 0',16,lambda a,b:a^b,mul,lambda a:a&1)

def z4dual():
    # Z/4[t]/(2t,t^3), bits 0-1 constant, bit 2 t, bit 3 t^2.
    def add(a,b):return ((a+b)&3)|((a^b)&12)
    def mul(a,b):
        v=(a*b)&3
        x=((a&1)*((b>>2)&1))^((b&1)*((a>>2)&1))
        y=((a&1)*((b>>3)&1))^((b&1)*((a>>3)&1))^(((a>>2)&1)*((b>>2)&1))
        return v|(x<<2)|(y<<3)
    return Ring('Z4[t]/(2t,t^3)',16,add,mul,lambda a:a&1)

if __name__=='__main__':
    rings=[Ring('F2',2,lambda a,b:a^b,lambda a,b:a*b,lambda a:a),
           Ring('Z4',4,lambda a,b:(a+b)%4,lambda a,b:(a*b)%4,lambda a:a&1),
           Ring('F2[t]/t^3',8,lambda a,b:a^b,poly2,lambda a:a&1),
           radical_ring(False),radical_ring(True),z4dual()]
    for R in rings:R.verify()
    for q in (2,4,8):
        # A_r and B_r have equal sizes, but different square-map ranks.
        for r in range(1,7):
            Q=q**(1+3*r); m=q**(5*r)
            assert m*Fraction(1,Q*Q)==Fraction(1,q**(r+2))
            assert m*Fraction(q**r,Q*Q)==Fraction(1,q*q)
    print('PASS: all exact checks and opposite-limit series identities.')
