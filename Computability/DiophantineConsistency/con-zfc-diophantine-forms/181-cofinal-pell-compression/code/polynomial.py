"""Exact sparse integer polynomials. No external dependencies."""
from collections import defaultdict
from itertools import product

def clean(p):
    return {tuple(m): int(c) for m, c in p.items() if c}

def poly(terms):
    p = defaultdict(int)
    for c, m in terms:
        p[tuple(sorted(m))] += c
    return clean(p)

def terms(p):
    return [[c, list(m)] for m, c in sorted(clean(p).items())]

def add(*ps):
    p = defaultdict(int)
    for q in ps:
        for m, c in q.items():
            p[m] += c
    return clean(p)

def scale(c, p):
    return clean({m: c*d for m, d in p.items()})

def mul(p, q):
    r = defaultdict(int)
    for m, c in p.items():
        for n, d in q.items():
            r[tuple(sorted(m+n))] += c*d
    return clean(r)

def var(i):
    return {(i,): 1}

def const(c):
    return {(): c} if c else {}

def degree(p):
    return max(map(len,p), default=0)

def subst(p, i, q):
    result = {}
    powers = {0: const(1), 1: q}
    for m, c in p.items():
        n = m.count(i)
        if not n:
            result = add(result, {m: c})
            continue
        if n not in powers:
            for j in range(2,n+1):
                powers.setdefault(j, mul(powers[j-1],q))
        rem = tuple(x for x in m if x != i)
        result = add(result, mul({rem:c},powers[n]))
    return result

def reindex(p, keep):
    ren = {v:i for i,v in enumerate(keep)}
    result = {}
    for m,c in p.items():
        if any(v not in ren for v in m):
            raise ValueError('deleted coordinate is still used')
        result[tuple(sorted(ren[v] for v in m))] = c
    return clean(result)

def expand(eq):
    return add(*(mul(poly(r['terms']),poly(r['terms'])) for r in eq['residuals']))

def evaluate(p, point):
    value = 0
    for m,c in p.items():
        a = c
        for i in m:
            a *= point[i]
        value += a
    return value

def metric(eq):
    p=expand(eq)
    return dict(variables=len(eq['variables']), residuals=len(eq['residuals']),
                degree=degree(p), monomials=len(p), height=max(map(abs,p.values())),
                residual_height=max(abs(c) for r in eq['residuals'] for c,_ in r['terms']),
                residual_monomials=sum(len(r['terms']) for r in eq['residuals']))
