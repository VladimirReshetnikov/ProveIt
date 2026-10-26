"""Exact sparse polynomial arithmetic for the source producer."""

from collections import defaultdict

import json, copy

def add(*ps):
    z=defaultdict(int)
    for p in ps:
        for m,c in p.items(): z[m]+=c
    return {m:c for m,c in z.items() if c}

def scale(k,p): return {m:k*c for m,c in p.items() if k*c}

def sub(p,q): return add(p,scale(-1,q))

def mul(p,q):
    z=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items(): z[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in z.items() if c}

def const(c): return {():c} if c else {}

def var(i): return {(i,):1}

def terms(p): return [[c,list(m)] for m,c in sorted(p.items())]

def poly(ts): return {tuple(m):c for c,m in ts}

def canonical(x): return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()

def subst(p,i,q):
    out={}
    for m,c in p.items():
        a=const(c)
        for j in m: a=mul(a,q if j==i else var(j))
        out=add(out,a)
    return out

def degree(p): return max(map(len,p),default=0)

def compact(eq):
    live=sorted({i for r in eq['residuals'] for _,m in r['terms'] for i in m})
    ren={i:j for j,i in enumerate(live)}
    new=copy.deepcopy(eq)
    new['variables']=[eq['variables'][i] for i in live]
    new['residuals']=[dict(r,terms=[[c,[ren[i] for i in m]] for c,m in r['terms']]) for r in eq['residuals']]
    return new,ren

def expand(eq):
    ans={}
    for r in eq['residuals']:
        p=poly(r['terms']);ans=add(ans,mul(p,p))
    return ans
