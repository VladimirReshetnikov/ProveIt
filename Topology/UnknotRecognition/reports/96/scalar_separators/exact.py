"""Small exact linear algebra. Standard library only; no floating point."""
from fractions import Fraction as F
from functools import reduce
from itertools import combinations
from math import gcd, lcm


def rref(rows, n):
    a = [[F(v) for v in row] for row in rows]
    if any(len(row) != n for row in a):
        raise ValueError('ragged matrix')
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(a)) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        q = a[r][c]
        a[r] = [v/q for v in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                q = a[i][c]
                a[i] = [u-q*v for u,v in zip(a[i],a[r])]
        piv.append(c)
        r += 1
        if r == len(a):
            break
    return a[:r], piv


def nullspace(rows, n):
    a, piv = rref(rows,n)
    free = [j for j in range(n) if j not in piv]
    ans=[]
    for j in free:
        v=[F(0)]*n
        v[j]=F(1)
        for i,p in enumerate(piv):
            v[p]=-a[i][j]
        ans.append(tuple(v))
    return ans


def rank(rows,n):
    return len(rref(rows,n)[1])


def primitive(v, canonical_sign=False):
    v=[F(x) for x in v]
    den=lcm(*(x.denominator for x in v)) if v else 1
    w=[int(x*den) for x in v]
    g=reduce(gcd,(abs(x) for x in w),0)
    if not g:
        return tuple(w)
    w=[x//g for x in w]
    if canonical_sign and next(x for x in w if x)!=abs(next(x for x in w if x)):
        w=[-x for x in w]
    return tuple(w)


def dot(a,b):
    return sum((F(x)*F(y) for x,y in zip(a,b)),F(0))


def rays_by_zeros(rows,n,pairs=()):
    """All admissible rays via (raw-nullity minus one) active coordinate rows.

    A local ray budget is intentionally not implicit. Callers can preflight
    the binomial count and decline a large model before invoking this routine.
    """
    K=nullspace(rows,n)
    d=len(K)
    if not d:
        return (), {'raw_nullity':0,'candidates':0}
    found=set()
    candidates=0
    for zeros in combinations(range(n),d-1):
        candidates+=1
        equations=[[K[h][j] for h in range(d)] for j in zeros]
        direction=nullspace(equations,d)
        if len(direction)!=1:
            continue
        v=[dot([K[h][j] for h in range(d)],direction[0]) for j in range(n)]
        if all(x<=0 for x in v):
            v=[-x for x in v]
        if not any(v) or any(x<0 for x in v):
            continue
        if any(v[i] and v[j] for i,j in pairs):
            continue
        found.add(primitive(v))
    return tuple(sorted(found)), {'raw_nullity':d,'candidates':candidates}


def rays_by_supports(rows,n,pairs=()):
    """Independent, deliberately exponential oracle: enumerate positive supports.

    Used by tests and the offline negative-certificate verifier, not by the
    production ray enumerator. It shares only elementary rational arithmetic.
    """
    ans=set()
    for mask in range(1,1<<n):
        S=[j for j in range(n) if mask>>j&1]
        if any((mask>>i&1) and (mask>>j&1) for i,j in pairs):
            continue
        kernel=nullspace([[row[j] for j in S] for row in rows],len(S))
        if len(kernel)!=1:
            continue
        v=kernel[0]
        if all(x<0 for x in v):
            v=tuple(-x for x in v)
        if not all(x>0 for x in v):
            continue
        full=[F(0)]*n
        for j,x in zip(S,v):
            full[j]=x
        ans.add(primitive(full))
    return tuple(sorted(ans))
