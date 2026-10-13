"""Small exact rational linear algebra; no floating-point predicates."""
from fractions import Fraction as Q
from math import gcd, lcm
from functools import reduce


def rational(value):
    if isinstance(value, bool) or isinstance(value, float):
        raise ValueError('rational input must be int, Fraction, or rational string')
    if not isinstance(value, (int, Q, str)):
        raise ValueError('unsupported rational input')
    return Q(value)


def matrix(rows, n):
    ans = tuple(tuple(rational(v) for v in row) for row in rows)
    if any(len(row) != n for row in ans):
        raise ValueError('matrix row has wrong length')
    return ans


def dot(a, b):
    if len(a) != len(b):
        raise ValueError('dot dimension mismatch')
    return sum((x*y for x,y in zip(a,b)), Q(0))


def rref(rows, n):
    a = [list(map(Q, r)) for r in rows]
    if any(len(r) != n for r in a):
        raise ValueError('rref dimension mismatch')
    pivots = []
    for j in range(n):
        p = next((i for i in range(len(pivots),len(a)) if a[i][j]), None)
        if p is None:
            continue
        i = len(pivots)
        a[i], a[p] = a[p], a[i]
        t = a[i][j]
        a[i] = [v/t for v in a[i]]
        for h in range(len(a)):
            if h != i and a[h][j]:
                t = a[h][j]
                a[h] = [u-t*v for u,v in zip(a[h], a[i])]
        pivots.append(j)
        if len(pivots) == len(a):
            break
    return tuple(tuple(r) for r in a), tuple(pivots)


def rank(rows, n):
    return len(rref(rows,n)[1])


def nullspace(rows, n):
    a,p = rref(rows,n)
    free = [j for j in range(n) if j not in p]
    out=[]
    for j in free:
        v=[Q(0)]*n; v[j]=Q(1)
        for i,h in enumerate(p):
            v[h]=-a[i][j]
        out.append(tuple(v))
    return tuple(out)


def solve_unique(a, b, n):
    """Solve a possibly overdetermined system, or return None."""
    if len(a) != len(b):
        raise ValueError('rhs dimension mismatch')
    aug,p = rref([tuple(row)+(Q(v),) for row,v in zip(a,b)],n+1)
    if n in p or len([j for j in p if j<n]) != n:
        return None
    x=[Q(0)]*n
    for i,j in enumerate(p):
        x[j]=aug[i][-1]
    return tuple(x)


def primitive(v, sign_canonical=False):
    den = lcm(*(a.denominator for a in map(Q,v))) if v else 1
    ints=[int(Q(a)*den) for a in v]
    g=reduce(gcd,(abs(a) for a in ints),0)
    if not g:
        return tuple(ints)
    ints=[a//g for a in ints]
    if sign_canonical and next(a for a in ints if a) < 0:
        ints=[-a for a in ints]
    return tuple(ints)
