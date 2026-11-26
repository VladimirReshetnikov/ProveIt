#!/usr/bin/env python3
"""Exact A5 tensor/induction certificate checks; Python standard library only.

These finite checks do not prove an analytic estimate or certify literature
novelty. The manuscript supplies the general analytic/group-theoretic proofs.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import permutations
from collections import Counter, deque
import json
from pathlib import Path

@dataclass(frozen=True)
class Quad:
    a: Q = Q(0)
    b: Q = Q(0)
    def __post_init__(self):
        object.__setattr__(self, 'a', Q(self.a))
        object.__setattr__(self, 'b', Q(self.b))
    @staticmethod
    def of(x): return x if isinstance(x, Quad) else Quad(x)
    def __add__(self, x):
        x=self.of(x); return Quad(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self): return Quad(-self.a,-self.b)
    def __sub__(self,x): return self+-self.of(x)
    def __rsub__(self,x): return self.of(x)+-self
    def __mul__(self,x):
        x=self.of(x); return Quad(self.a*x.a+5*self.b*x.b,self.a*x.b+self.b*x.a)
    __rmul__=__mul__
    def __truediv__(self,x):
        x=self.of(x); n=x.a*x.a-5*x.b*x.b
        return self*Quad(x.a/n,-x.b/n)
    def __pow__(self,n):
        assert n>=0
        ans=Quad(1); base=self
        while n:
            if n&1: ans=ans*base
            base=base*base; n//=2
        return ans
    def integer(self):
        assert self.b==0 and self.a.denominator==1, self
        return int(self.a)
    def __str__(self): return f'{self.a}+({self.b})sqrt(5)'

def mul(a,b): return tuple(a[b[i]] for i in range(5))
def inv(a): return tuple(a.index(i) for i in range(5))
def even(p): return sum(p[i]>p[j] for i in range(5) for j in range(i+1,5))%2==0
G=tuple(p for p in permutations(range(5)) if even(p)); one=tuple(range(5))
assert len(G)==60

def closure(gens):
    generators=tuple(set(gens)|{inv(x) for x in gens})
    seen={one}; todo=[one]
    while todo:
        a=todo.pop()
        for b in generators:
            c=mul(a,b)
            if c not in seen: seen.add(c); todo.append(c)
    return frozenset(seen)

def power(g,k):
    r=one
    for _ in range(k): r=mul(r,g)
    return r

def order(g):
    r=one
    for k in range(1,61):
        r=mul(r,g)
        if r==one: return k
    raise AssertionError

a=(1,2,3,4,0)
b=(0,4,3,2,1)
c=(0,2,3,1,4)
C5=closure([a]); D5=closure([a,b]); A4=frozenset(g for g in G if g[0]==0)
V4=frozenset(g for g in A4 if order(g) in (1,2))
C3gen=(1,2,0,3,4); S3flip=(1,0,2,4,3); S3=closure([C3gen,S3flip])
assert (len(C5),len(D5),len(A4),len(V4),len(S3))==(5,10,12,4,6)

reps=[one,next(g for g in G if order(g)==2),c,a,power(a,2)]
classes=[frozenset(mul(mul(x,g),inv(x)) for x in G) for g in reps]
sizes=[len(c) for c in classes]
assert sizes==[1,15,20,12,12]
assert len(set().union(*classes))==60
classof={g:i for i,C in enumerate(classes) for g in C}
ph=Quad(Q(1,2),Q(1,2)); ps=Quad(Q(1,2),Q(-1,2))
X=[[Quad(1)]*5,
   [Quad(3),Quad(-1),Quad(0),ph,ps],
   [Quad(3),Quad(-1),Quad(0),ps,ph],
   list(map(Quad,[4,0,1,-1,-1])),
   list(map(Quad,[5,1,-1,0,0]))]

def ip(f,h): return sum(sz*a*b for sz,a,b in zip(sizes,f,h))/60
for i in range(5):
    for j in range(5): assert ip(X[i],X[j]).integer()==int(i==j)
def decomp(f): return [ip(f,row).integer() for row in X]
def char_value(coeff,g): return sum(n*row[classof[g]] for n,row in zip(coeff,X))
def vadd(*vs): return [sum(v[i] for v in vs) for i in range(5)]
def scale(a,v): return [a*x for x in v]

# Direct induction from actual subgroup linear characters.
exp5={power(a,k):k for k in range(5)}
exp3={mul(v,power(c,k)):k for v in V4 for k in range(3)}
assert len(exp3)==12

def induce(H,typ):
    out=[]
    for g in reps:
        conj=[mul(mul(inv(x),g),x) for x in G]
        inside=[h for h in conj if h in H]
        if typ=='sign': val=Quad(sum(1 if h in C5 else -1 for h in inside))/len(H)
        elif typ=='fifth':
            cnt=Counter(exp5[h] for h in inside)
            assert cnt[1]==cnt[4] and cnt[2]==cnt[3]
            val=(Quad(cnt[0])+cnt[1]*Quad(Q(-1,2),Q(1,2))+cnt[2]*Quad(Q(-1,2),Q(-1,2)))/len(H)
        elif typ=='third':
            cnt=Counter(exp3[h] for h in inside); assert cnt[1]==cnt[2]
            val=Quad(cnt[0]-cnt[1])/len(H)
        else: raise AssertionError
        out.append(val)
    return out
A=decomp(induce(D5,'sign')); B=decomp(induce(C5,'fifth')); C=decomp(induce(A4,'third'))
assert A==[0,1,1,0,0] and B==[0,1,0,1,1] and C==[0,0,0,0,1]
powers={k:decomp([v**k for v in X[1]]) for k in range(1,7)}
F=powers[4]; reg=[1,3,3,4,5]; triv=[1,0,0,0,0]
assert F==[3,6,3,4,7]
assert scale(4,F)==vadd(reg,scale(11,triv),scale(9,A),scale(12,B),scale(11,C))

# Enumerate every subgroup by adjoining every possible extra generator.
subgroups={frozenset([one]):()}; todo=deque(subgroups)
while todo:
    H=todo.popleft(); gens=subgroups[H]
    for g in G:
        if g in H: continue
        J=closure(gens+(g,))
        if J not in subgroups:
            subgroups[J]=gens+(g,); todo.append(J)
proper=[H for H in subgroups if len(H)<60]
maximal=[H for H in proper if not any(H<J for J in proper)]
assert len(subgroups)==59
maxcounts=dict(sorted(Counter(map(len,maximal)).items()))
assert maxcounts=={6:10,10:6,12:5}
# Every maximal subgroup is conjugate to the displayed A4, D5 or S3.
for H in maximal:
    model={6:S3,10:D5,12:A4}[len(H)]
    assert any(H==frozenset(mul(mul(x,h),inv(x)) for h in model) for x in G)

witness=[0,-1,1,1,0]
# A4 restriction is its natural four-point permutation character.
for g in A4:
    assert char_value(witness,g)==Quad(sum(g[i]==i for i in range(1,5)))
# D5 restriction is twice one 2D irreducible induced from C5.
for g in D5:
    if g not in C5: val=Quad(0)
    else:
        k=exp5[g]
        val=Quad(4) if k==0 else (Quad(-1,-1) if k in (1,4) else Quad(-1,1))
    assert char_value(witness,g)==val
# S3 restriction = natural three-point permutation + sign on three points.
for g in S3:
    restricted=tuple(g[i] for i in range(3))
    parity=sum(restricted[i]>restricted[j] for i in range(3) for j in range(i+1,3))%2
    val=sum(g[i]==i for i in range(3)) + (-1 if parity else 1)
    assert char_value(witness,g)==Quad(val)

pair=lambda v,w:sum(a*b for a,b in zip(v,w))
assert pair(reg,witness)==4
assert [pair(powers[k],witness) for k in range(1,5)]==[-1,-1,-1,1]
# Exact n_0=0 cone extreme rays and optimal ratios.
rays=[(1,0,0,0),(0,1,0,0),(-1,1,1,0),(1,-1,1,0),(-1,1,0,1),(1,-1,0,1)]
ratios=[]
for x,y,z,w in rays:
    assert min(z,w,x+y,x+z+w,y+z+w)>=0
    ratios.append(Q(6*x+3*y+4*z+7*w,3*x+3*y+4*z+5*w))
assert min(ratios)==Q(1,4) and max(ratios)==2
# Identity domination is strictly weaker in this example.
gaps={k:(X[1][0]**k-sum(sz*v**k for sz,v in zip(sizes[1:],X[1][1:]))).integer() for k in [2,4,6]}
assert gaps=={2:-42,4:-18,6:498}

result={
 'status':'PASS; exact finite algebra only',
 'group_order':60,'subgroups':59,'maximal_subgroup_counts':maxcounts,
 'induced_multiplicities':{'D5_sign':A,'C5_lambda':B,'A4_omega':C},
 'tensor_multiplicities':powers,'tensor_four_dimension':81,
 'positive_certificate':'4*chi^4 = Reg + 11*1 + 9*Ind_D5(sign) + 12*Ind_C5(lambda) + 11*Ind_A4(omega)',
 'witness':witness,'witness_degree':4,
 'witness_tensor_orders':[pair(powers[k],witness) for k in range(1,5)],
 'cone_extreme_rays':rays,'exact_e_over_d_ratios':[str(r) for r in ratios],
 'identity_domination_gaps':gaps,
 'scope':'Does not prove a prime-sum bound, actual existence of a zero realizing the witness, or novelty.'}
output=Path(__file__).resolve().parent.parent / 'data' / 'a5_tensor_certificate.json'
output.parent.mkdir(exist_ok=True)
output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
