"""Depth-preserving normal form for the convergent Cayley shuffle ideal.

Adapted letters, in the Lyndon order used in the proof:
    Z=0, Y=1, H=2, B=3, X=4.
C reverses a word, swaps Z,X, and multiplies by (-1)^number(H).
K multiplies a word by (-1)^number(Y).
All arithmetic in this implementation is rational and exact.
"""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations
from math import comb, factorial

Z,Y,H,B,X=range(5)

def add(out,p,scale=1):
    for w,c in p.items():
        v=out.get(w,0)+scale*c
        if v:out[w]=v
        else:out.pop(w,None)
    return out

@lru_cache(None)
def shuffle(u,v):
    if not u:return {v:1}
    if not v:return {u:1}
    out={}
    for w,c in shuffle(u[1:],v).items():add(out,{(u[0],)+w:c})
    for w,c in shuffle(u,v[1:]).items():add(out,{(v[0],)+w:c})
    return out

def multiply(p,q):
    out={}
    for u,a in p.items():
        for v,b in q.items():add(out,shuffle(u,v),a*b)
    return out

def apply(f,p):
    out={}
    for w,c in p.items():add(out,f(w),c)
    return out

def admissible(w):return not w or (w[0]!=X and w[-1]!=Z)
def depth(w):return len(w)-w.count(Z)
def degree(w):return w.count(Z),w.count(X)
def parity(w):return w.count(Y)%2

def cayley(w):
    out=tuple(X if a==Z else Z if a==X else a for a in reversed(w))
    return {out:(-1)**w.count(H)}

def conjugate(w):return {w:(-1)**w.count(Y)}

@lru_cache(None)
def regularize(w):
    """Shuffle-coordinate substitution X=Z=0; not literal word erasure."""
    l=0
    while l<len(w) and w[l]==X:l+=1
    r=0
    while r<len(w) and w[-1-r]==Z:r+=1
    out={}
    for a in range(l+1):
        for b in range(r+1):
            middle=w[a:len(w)-b] if b else w[a:]
            term=multiply({(X,)*a:1},multiply({middle:1},{(Z,)*b:1}))
            add(out,term,(-1)**(a+b))
    assert all(admissible(v) and degree(v)==degree(w) for v in out)
    return out

@lru_cache(None)
def permutation_data(n):
    out=[]
    for p in permutations(range(n)):
        inv=[0]*n
        for i,j in enumerate(p):inv[j]=i
        desc=sum(inv[j]>inv[j+1] for j in range(n-1))
        out.append((p,Q((-1)**desc,n*comb(n-1,desc))))
    return out

@lru_cache(None)
def eulerian(w):
    if not w:return {}
    out={}
    for p,c in permutation_data(len(w)):
        add(out,{tuple(w[j] for j in p):c})
    return out

@lru_cache(None)
def lift(w):return apply(regularize,eulerian(w))

@lru_cache(None)
def oriented_lift(w):
    p=lift(w);a,b=degree(w)
    if a>b:return p
    if a<b:return apply(cayley,p)
    out={w:c/2 for w,c in p.items()}
    return add(out,apply(cayley,p),Q(1,2))

@lru_cache(None)
def convolution_power(w,k):
    if k==0:return {():1} if not w else {}
    if len(w)<k:return {}
    out={}
    for j in range(1,len(w)-k+2):
        a=oriented_lift(w[:j])
        if a:add(out,multiply(a,convolution_power(w[j:],k-1)))
    return out

@lru_cache(None)
def projection(w):
    if not w:return {():1}
    out={}
    for k in range(1,len(w)+1):add(out,convolution_power(w,k),Q(1,factorial(k)))
    assert all(admissible(v) and depth(v)<=depth(w) for v in out)
    return out


def eulerian_by_cuts(w):
    """Independent consecutive-cut definition of the Eulerian logarithm."""
    if not w:return {}
    out={};n=len(w)
    for mask in range(1<<(n-1)):
        cuts=[0]+[j for j in range(1,n) if mask>>(j-1)&1]+[n]
        term={():1}
        for a,b in zip(cuts,cuts[1:]):term=multiply(term,{w[a:b]:1})
        k=len(cuts)-1;add(out,term,Q((-1)**(k-1),k))
    return out
