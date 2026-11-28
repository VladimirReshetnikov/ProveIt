#!/usr/bin/env python3
"""Exact certificate checker; standard library only. No optimizer or character tables.
See paper.tex for the group-theoretic proof and interpretation of row identities.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import cache
from pathlib import Path
from math import factorial, gcd, isqrt, prod
import json
import sys

@cache
def partitions(n, cap=None):
    if not n:
        return ((),)
    cap = n if cap is None else min(cap, n)
    return tuple((k,) + t for k in range(1, cap + 1)
                 for t in partitions(n - k, k))


def centralizer(t):
    return prod(k**m * factorial(m) for k, m in Counter(t).items())


def typ(p):
    remaining = set(range(len(p)))
    t = []
    while remaining:
        v = min(remaining)
        k = 0
        while v in remaining:
            remaining.remove(v)
            v = p[v]
            k += 1
        t.append(k)
    return tuple(sorted(t, reverse=True))


@cache
def trace(d, j):
    # Sum of primitive d-th roots to power j, using the partition of all roots
    # by exact order. This is independent of search.py's Mobius implementation.
    return (d if j % d == 0 else 0) - sum(trace(e, j) for e in range(1, d) if d % e == 0)


def mean(d, j):
    return Q(trace(d, j), sum(gcd(h, d) == 1 for h in range(1, d+1)))


def prime(p):
    return p >= 2 and all(p % h for h in range(2, isqrt(p)+1))


@cache
def block(desc):
    kind, k, *args = desc
    assert isinstance(k, int) and k >= 2
    r = defaultdict(Q)
    if kind == 'C':
        d, = args
        assert d >= 1 and k % d == 0
        for j in range(k):
            r[typ([(i+j) % k for i in range(k)])] += mean(d, j)
    elif kind == 'D':
        a, b = args
        assert k >= 3 and a in (0,1) and b in (0,1) and a*k % 2 == 0
        for j in range(k):
            for e in (0,1):
                perm = [((-1)**e*i+j) % k for i in range(k)]
                r[typ(perm)] += (-1)**(a*j+b*e)
    elif kind in ('S','A'):
        if kind == 'S':
            a, = args
            assert a in (0,1)
        else:
            assert k >= 3 and args == []
            a = 0
        for t in partitions(k):
            if kind == 'A' and (k-len(t)) % 2:
                continue
            r[t] = Q(factorial(k)//centralizer(t) * (-1)**(a*(k-len(t))))
    elif kind == 'F':
        d, e = args
        assert prime(k) and d >= 2 and (k-1) % d == 0 and e >= 1 and d % e == 0
        # Explicit multiplier of exact order d; enumerate the affine group.
        a = next(a for a in range(1,k) if pow(a,d,k)==1 and
                 all(pow(a,j,k)!=1 for j in range(1,d)))
        for j in range(d):
            for b in range(k):
                r[typ([(pow(a,j,k)*i+b) % k for i in range(k)])] += mean(e,j)
    else:
        raise ValueError(desc)
    assert r[(1,)*k] == 1
    return {t: x for t,x in r.items() if x}


def multiply(A, B):
    R = defaultdict(Q)
    for s,a in A.items():
        for t,b in B.items():
            R[tuple(sorted(s+t, reverse=True))] += a*b
    return {t: x for t,x in R.items() if x}


def row(n, descriptors):
    k = sum(t[1] for t in descriptors)
    assert k <= n
    r = {(1,)*(n-k): Q(1)}
    for t in descriptors:
        r = multiply(r, block(tuple(t)))
    # Additional independent sanity checks: every summand kills the trivial
    # and standard characters, as required by the target's vanishing pairings.
    assert sum(r.values()) == 0
    assert sum(x*(t.count(1)-1) for t,x in r.items()) == 0
    assert r[(1,)*n] == 1
    return r


def verify(path):
    data=json.loads(path.read_text())
    n=data['n']
    assert n >= 3
    P = partitions(n)
    target = {t: Q(2, (n-1)*centralizer(t)) for t in P}
    target[(1,)*n] += Q(n-3,n-1)
    target[(2,)+(1,)*(n-2)] -= 1
    actual=defaultdict(Q)
    maxbits=0
    for entry in data['terms']:
        w=Q(entry['weight'])
        assert w > 0
        maxbits=max(maxbits,w.numerator.bit_length(),w.denominator.bit_length())
        for t,x in row(n,entry['blocks']).items():
            actual[t] += w*x
    for t in set(actual)|set(target):
        assert actual[t] == target.get(t,0), (n,t,actual[t],target.get(t,0))
    # Verify both moment identities on the target itself.
    assert sum(actual.values()) == 0
    assert sum(x*(t.count(1)-1) for t,x in actual.items()) == 0
    print(f'S_{n}: PASS; {len(P)} cycle types, {len(data["terms"])} positive rows; max coefficient bit length {maxbits}')


def asymptotic_constant():
    # Bound S = sum_{p odd} prod_{q<p}(1-1/q)/(p(p-1)).
    cutoff=10000
    s=Q(0); density=Q(1,2)
    for p in range(3,cutoff+1,2):
        if prime(p):
            s+=density/Q(p*(p-1)); density*=Q(p-1,p)
    lo=Q(4,3)*(1+s)
    hi=Q(4,3)*(1+s+density/cutoff)
    # The following decimal enclosure is verified, not inferred from floats.
    assert Q('1.48335') < lo < hi < Q('1.48337')
    print('Asymptotic constant: PASS; 1.48335 < C < 1.48337')
    print(f'  narrower floating display (not used in verification): [{float(lo):.12f}, {float(hi):.12f}]')

if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without Python -O: assertions are the certificate checks.')
    root=Path(__file__).resolve().parent
    paths=[Path(x) for x in sys.argv[1:]] or [root/f'cert_{n}.json' for n in range(13,17)]
    for p in paths:
        verify(p)
    asymptotic_constant()
