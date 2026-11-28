#!/usr/bin/env python3
"""Exact finite regressions for the Gram-duality proposal (standard library only)."""
from fractions import Fraction as F
from itertools import product
from math import lcm


def mat(rows): return [[F(x) for x in r] for r in rows]
def tr(a): return list(map(list, zip(*a)))
def mm(a,b): return [[sum(x*y for x,y in zip(r,c)) for c in tr(b)] for r in a]
def sc(s,a): return [[s*x for x in r] for r in a]
def eye(n): return mat([[int(i==j) for j in range(n)] for i in range(n)])
def diag(xs): return mat([[x if i==j else 0 for j in range(len(xs))] for i,x in enumerate(xs)])
def integral(a): return all(x.denominator==1 for r in a for x in r)
def inv(a):
    n=len(a); b=[r[:]+s[:] for r,s in zip(a,eye(n))]
    for j in range(n):
        k=next(k for k in range(j,n) if b[k][j]); b[j],b[k]=b[k],b[j]
        d=b[j][j]; b[j]=[x/d for x in b[j]]
        for k in range(n):
            if k!=j:
                d=b[k][j]; b[k]=[x-d*y for x,y in zip(b[k],b[j])]
    return [r[n:] for r in b]

# Both hook and stabilizer factors may be necessary.
G=diag([1,2,1]); H=diag([2,1,2]); h=2
assert mm(G,H)==sc(h,eye(3))
L=mat([[0,1,0]]); K=mat([[F(1,3)]]); n=3
adj=mm(mm(inv(G),tr(L)),K)
assert mm(L,adj)==mat([[F(1,6)]])
assert integral(sc(n*h,mm(L,adj)))
assert not integral(sc(n,mm(L,adj))) and not integral(sc(h,mm(L,adj)))
print('PASS: symmetric-square example and necessity of both factors')

count=0
for G in [mat([[2,1],[1,2]]),diag([1,2]),mat([[5,2],[2,3]])]:
    Gi=inv(G); h=lcm(*(x.denominator for r in Gi for x in r)); H=sc(h,Gi)
    assert integral(H) and mm(G,H)==sc(h,eye(2)) and mm(H,G)==sc(h,eye(2))
    for n,K in [(2,mat([[F(3,2),F(1,2)],[F(1,2),1]])),(3,diag([F(1,3),F(2,3)]))]:
        assert integral(sc(n,K))
        for entries in product(range(-2,3),repeat=4):
            L=mat([entries[:2],entries[2:]])
            adj=mm(mm(Gi,tr(L)),K)
            p=sc(n,mm(tr(L),K))  # columns correspond to all target basis vectors
            assert integral(p)
            assert integral(sc(n*h,adj))
            assert sc(n*h,adj)==mm(H,p)
            assert integral(sc(n*h,mm(L,adj)))
            count+=1
print(f'PASS: {count} exact matrix instances of integral adjoint and integral comparison')

# The lattice may be integral only in a transported basis, not the original coordinates.
R=mat([[F(3,5),F(-4,5)],[F(4,5),F(3,5)]])
assert mm(tr(R),R)==eye(2)
B=inv(R) # adapted basis; original coordinates are B times integral coefficients
A=mat([[1,2],[-3,1]]); L=mm(A,R); K=diag([F(1,3),F(2,3)])
assert mm(L,B)==A and not integral(L)
adj=mm(tr(L),K)
assert integral(sc(3,mm(R,adj))) and integral(sc(3,mm(L,adj)))
print('PASS: rational unitary transport with nonintegral original coordinates')

# Exact field Q(alpha,i), alpha^4=2, i^2=-1. Basis alpha^a i^b, a<4,b<2.
class E:
    def __init__(self, terms=0):
        if isinstance(terms,E): self.t=terms.t.copy()
        elif isinstance(terms,dict): self.t={k:F(v) for k,v in terms.items() if v}
        else: self.t={(0,0):F(terms)} if terms else {}
    def __add__(self,o):
        o=E(o); d=self.t.copy()
        for k,v in o.t.items(): d[k]=d.get(k,0)+v
        return E(d)
    __radd__=__add__
    def __neg__(self): return E({k:-v for k,v in self.t.items()})
    def __sub__(self,o): return self+-E(o)
    def __rsub__(self,o): return E(o)+-self
    def __mul__(self,o):
        o=E(o); d={}
        for (a,b),x in self.t.items():
            for (c,e),y in o.t.items():
                q,r=divmod(a+c,4); s,t=divmod(b+e,2); k=(r,t)
                d[k]=d.get(k,0)+x*y*2**q*(-1)**s
        return E(d)
    __rmul__=__mul__
    def __pow__(self,n):
        out=E(1)
        for _ in range(n): out=out*self
        return out
    def __eq__(self,o): return self.t==E(o).t
    def conj(self): return E({(a,b):v*(-1)**b for (a,b),v in self.t.items()})
    def sigma(self,k):
        return sum((E({(a,b):v})*I**((k*a)%4) for (a,b),v in self.t.items()),E())

alpha=E({(1,0):1}); I=E({(0,1):1})
assert alpha**4==2 and I**2==-1
assert (alpha.conj()*alpha).sigma(1)==-(alpha**2)
assert alpha.sigma(1).conj()*alpha.sigma(1)==alpha**2

def pair(v,z,G): return sum((v[i].conj()*G[i][j]*z[j] for i in range(len(v)) for j in range(len(z))),E())
G=mat([[2,1],[1,2]])
zs=[[alpha+I,alpha**2-I*alpha],[I*alpha**3,2-alpha],[E(0),E(0)]]
vs=[[alpha,I*alpha],[E(1)+I,alpha**3],[I,alpha+2]]
count=0
for k,z,v in product(range(4),zs,vs):
    assert pair(v,z,G).sigma(k)==pair([a.sigma(-k) for a in v],[a.sigma(k) for a in z],G)
    witness=[a.sigma(2*k) for a in z]
    assert [a.sigma(-k) for a in witness]==[a.sigma(k) for a in z]
    w=[a.sigma(k) for a in z]
    assert pair(witness,z,G).sigma(k)==pair(w,w,G)
    count+=1
print(f'PASS: {count} exact paired-conjugation identities and explicit dual witnesses')

# An adjoint on the full coordinate space also satisfies the exact paired identity.
L=[[alpha+I, E(1)-alpha],[I*alpha,E(2)]]
z=[alpha+I*alpha**2, E(2)-I]
G=diag([1,2]); K=diag([3,1]); Gi=inv(G)
# No complex numerical operations: adjoint = G^-1 conjugate-transpose(L) K.
adj=mm(mm(Gi,[[a.conj() for a in r] for r in tr(L)]),K)
u=[r[0] for r in mm(adj,[[a] for a in z])]
for k,v in product(range(4),vs):
    Lv=[r[0] for r in mm(L,[[a] for a in v])]
    assert pair(v,u,G)==pair(Lv,z,K)
    assert pair(v,u,G).sigma(k)==pair([a.sigma(-k) for a in Lv],[a.sigma(k) for a in z],K)
print('PASS: exact paired adjoint identity for a non-real gluing matrix')

assert F(2)+F(1,2)+F(1,12)==F(31,12)<3
assert F(2)+F(1,2)+F(2,12)==F(8,3)<3
# A common scalar cancels from the ratio of compressed determinants.
for d in range(9):
    for h in range(1,10):
        x,y=F(3,7)**d,F(5,11)**d
        assert (x/h**d)/(y/h**d)==x/y
print('PASS: scalar budgets and compression determinant ratio cancellation')
print('All exact finite regressions passed. These are not a Lean proof or verification of RH.')
