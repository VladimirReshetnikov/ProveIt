#!/usr/bin/env python3
"""Exact algebra certificates supporting the projective-frame proof.

Uses only the standard library. This does not replace the abstract proof of
projective duality, ideal arithmetic, or uniform analytic estimates.
"""
from fractions import Fraction as F
from pathlib import Path
import json
from collections import defaultdict


class K:
    """Q[eta], eta^2-eta+2=0, with exact rational coefficients."""
    def __init__(self, a=0, b=0):
        if isinstance(a, K): self.a, self.b = a.a, a.b
        else: self.a, self.b = F(a), F(b)
    def __add__(self, other):
        other=K(other); return K(self.a+other.a, self.b+other.b)
    __radd__=__add__
    def __neg__(self): return K(-self.a,-self.b)
    def __sub__(self, other): return self+-K(other)
    def __rsub__(self, other): return K(other)+-self
    def __mul__(self, other):
        other=K(other)
        return K(self.a*other.a-2*self.b*other.b,
                 self.a*other.b+self.b*other.a+self.b*other.b)
    __rmul__=__mul__
    def conj(self): return K(self.a+self.b,-self.b)
    def norm(self): return self.a*self.a+self.a*self.b+2*self.b*self.b
    def __eq__(self, other):
        other=K(other); return self.a==other.a and self.b==other.b
    def __hash__(self): return hash((self.a,self.b))
    def data(self): return [str(self.a),str(self.b)]


eta=K(0,1)
zero=K(0)
one=K(1)

def add(A,B): return [[x+y for x,y in zip(a,b)] for a,b in zip(A,B)]
def scale(c,A): return [[c*x for x in a] for a in A]
def mul(A,B):
    return [[sum((x*y for x,y in zip(a,b)),zero) for b in zip(*B)] for a in A]
def adj(A): return [[x.conj() for x in a] for a in zip(*A)]
def col(v): return [[x] for x in v]
def outer(v,w=None):
    return mul(col(v),adj(col(v if w is None else w)))
def mat_sum(terms):
    out=[[zero,zero],[zero,zero]]
    for c,A in terms: out=add(out,scale(K(c),A))
    return out
def vec_add(a,b): return tuple(x+y for x,y in zip(a,b))
def vec_scale(a,b): return tuple(a*x for x in b)
I=[[one,zero],[zero,one]]
H=[[one,eta],[eta.conj(),K(3)]]
Hinv=[[K(3),-eta],[-eta.conj(),one]]
assert mul(H,Hinv)==I
assert eta+eta.conj()==one and eta.norm()==2

# O_K^2 with this positive definite unimodular H is self-dual.
# Its orthonormal integral basis W obeys W* H W=I and W W*=H^-1.
W=[[-eta,one],[one,zero]]
Winv=[[zero,one],[one,eta]]
assert mul(W,Winv)==I
assert mul(mul(adj(W),H),W)==I
assert mul(W,adj(W))==Hinv
x=[(one,zero),(zero,one)]
y=[tuple(row[i] for row in Hinv) for i in range(2)]
theta=lambda v:mul(outer(v),H)
mixed=lambda v,w:mul(outer(v,w),H)
assert mat_sum((1,mixed(a,b)) for a,b in zip(x,y))==I

signed=defaultdict(int)
for a,b in zip(x,y):
    v=vec_add(a,vec_scale(eta,b))
    left=mat_sum([(1,theta(v)),(-1,theta(a)),(-2,theta(b))])
    right=mat_sum([(eta.conj(),mixed(a,b)),(eta,mixed(b,a))])
    assert left==right
    signed[v]+=1; signed[a]-=1; signed[b]-=2
assert mat_sum((z,theta(v)) for v,z in signed.items())==I

# Change to the orthonormal W basis. Coefficients remain in O_K.
signed_orth=defaultdict(int)
for v,z in signed.items():
    u=tuple(row[0] for row in mul(Winv,col(v)))
    assert all(c.a.denominator==c.b.denominator==1 for c in u)
    signed_orth[u]+=z
assert mat_sum((z,outer(v)) for v,z in signed_orth.items())==I

# Build a positive integral reserve containing every signed vector.
reserve=defaultdict(int,{v:1 for v in signed_orth})
C=mat_sum((c,outer(v)) for v,c in reserve.items())
assert C[0][0].b==C[1][1].b==0
off=-C[0][1]
a,b=int(off.a),int(off.b)
extra=[]
if a: extra.append((abs(a),(K(1 if a>0 else -1),one)))
if b: extra.append((abs(b),(vec_scale(K(1 if b>0 else -1),(eta,))[0],one)))
E=mat_sum((c,outer(v)) for c,v in extra)
q=1+max(int((C[i][i]+E[i][i]).a) for i in range(2))
for c,v in extra: reserve[v]+=c
for i,e in enumerate(x): reserve[e]+=q-int((C[i][i]+E[i][i]).a)
assert all(c>0 for c in reserve.values())
assert mat_sum((c,outer(v)) for v,c in reserve.items())==scale(K(q),I)

R=7
ceil=lambda a,b:-(-a//b)
k0=max(ceil(R+(q-1)*max(0,-signed_orth.get(v,0)),c)
       for v,c in reserve.items())
M0=q*k0
for M in range(M0,M0+3*q+1):
    k,r=divmod(M,q)
    coeff={v:k*c+r*signed_orth.get(v,0) for v,c in reserve.items()}
    assert min(coeff.values())>=R
    assert mat_sum((c,outer(v)) for v,c in coeff.items())==scale(K(M),I)

data={
    'status':'passed',
    'quadratic_relation':'eta^2-eta+2=0',
    'trace_eta':1,'norm_eta':2,
    'positive_unimodular_hermitian_gram':[[z.data() for z in a] for a in H],
    'signed_identity':[
        {'vector':[z.data() for z in v],'coefficient':c} for v,c in signed_orth.items()],
    'reserve':{
        'bound':q,'vectors':[
            {'vector':[z.data() for z in v],'multiplicity':c} for v,c in reserve.items()]},
    'threshold':{'required_multiplicity':R,'k0':k0,'M0':M0,
                 'bounds_checked':3*q+1},
    'scope':'Exact algebra identities and a nontrivial reserve certificate; not a formal proof of general projective-module or analytic results.'
}
out=Path(__file__).resolve().parents[1]/'certificates/algebra_certificates.json'
out.write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'status':'passed','reserve_bound':q,'threshold':M0,
                  'bounds_checked':3*q+1,'certificate':str(out)},indent=2))
