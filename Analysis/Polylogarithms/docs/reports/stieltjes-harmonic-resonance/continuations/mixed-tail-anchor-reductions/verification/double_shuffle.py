"""Exact rational research routines. See article.tex for conventions and proofs.

MZV words use descending indices. No numerical period-independence assumption
is used. The compiler accepts integer orders at least two.
"""
from research import *
from collections import Counter

@lru_cache(None)
def sh(u,v):
    if not u:return {v:1}
    if not v:return {u:1}
    out=Counter()
    for w,c in sh(u[1:],v).items():out[(u[0],)+w]+=c
    for w,c in sh(u,v[1:]).items():out[(v[0],)+w]+=c
    return dict(out)

def encode(w):return tuple(x for s in w for x in (0,)*(s-1)+(1,))
def decode(w):
    out=[];n=1
    for a in w:
        if a==0:n+=1
        else:out.append(n);n=1
    assert n==1
    return tuple(out)

def shuffle(u,v):return {decode(w):c for w,c in sh(encode(u),encode(v)).items()}
def admissible(n):return tuple(w for w in comps(n) if w[0]>=2)

def relations(n):
    words=admissible(n); idx={w:i for i,w in enumerate(words)}
    rows=[]; labels=[]
    def add(v,label):
        v={w:c for w,c in v.items() if c}
        if not v:return
        assert all(w in idx for w in v), v
        rows.append([v.get(w,0) for w in words]); labels.append(label)
    # ordinary and one-index-one regularized double shuffle
    for k in range(1,n-1):
      for u in ((1,),) if k==1 else admissible(k):
       for v in admissible(n-k):
        r=Counter(stuffle(u,v))
        for w,c in shuffle(u,v).items():r[w]-=c
        add(r,('ds',u,v))
    for w in words:
        dual=decode(tuple(1-x for x in reversed(encode(w))))
        if w!=dual:add({w:1,dual:-1},('dual',w))
    return words,S.Matrix(rows),labels

def vector(expr,words):
    expr=linearize(expr)
    return S.Matrix([[expr.coeff(Z(w)) for w in words]])

