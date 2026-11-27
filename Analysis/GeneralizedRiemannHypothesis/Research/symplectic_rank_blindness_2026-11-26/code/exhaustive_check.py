#!/usr/bin/env python3
"""Independent exhaustive check of the fixed-projection extension count.

Uses prime fields F_2 and F_3. No random sampling and no group generation:
enumerates every 2n-by-n matrix, retains full frames, groups by actual Gram
matrix and actual top projection, then compares against the block formula.
"""
from itertools import product
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path

def rank(rows, q):
    a = [list(row) for row in rows]
    if not a:
        return 0
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][j] % q), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        d = pow(a[r][j] % q, -1, q)
        a[r] = [(d*x) % q for x in a[r]]
        for i in range(len(a)):
            if i != r:
                d = a[i][j] % q
                a[i] = [(x-d*y) % q for x,y in zip(a[i],a[r])]
        r += 1
        if r == len(a):
            break
    return r

def gram(A, B, q):
    n = len(A)
    return tuple(tuple(sum(A[h][i]*B[h][j]-B[h][i]*A[h][j] for h in range(n))%q
                       for j in range(n)) for i in range(n))

def matvec(A, v, q):
    return tuple(sum(x*y for x,y in zip(row,v))%q for row in A)

def predicted(A, H, q):
    n = len(A)
    k = n-rank(A,q)
    vectors = list(product(range(q),repeat=n))
    K = [v for v in vectors if not any(matvec(A,v,q))]
    if any(sum(x*y for x,y in zip(v,matvec(H,w,q)))%q for v in K for w in K):
        return 0
    t = n-rank(list(A)+list(H),q)
    c = Fraction(q**(n*(n+1)//2 + k*(k-1)//2))
    for j in range(k-t+1,k+1):
        c *= 1-Fraction(1,q**j)
    assert c.denominator == 1
    return c.numerator

def check(q,n):
    matrices=[tuple(tuple(e[i*n:(i+1)*n]) for i in range(n))
              for e in product(range(q),repeat=n*n)]
    counts=Counter()
    gram_totals=Counter()
    full_frames=0
    for A in matrices:
        for B in matrices:
            if rank(A+B,q) == n:
                H=gram(A,B,q)
                counts[A,H]+=1
                gram_totals[H]+=1
                full_frames+=1
    checks=0
    for H in gram_totals:
        for A in matrices:
            assert counts[A,H] == predicted(A,H,q), (q,n,A,H,counts[A,H],predicted(A,H,q))
            checks+=1
    by_rank={}
    for H,total in gram_totals.items():
        rh=rank(H,q)
        by_rank.setdefault(rh,set()).add(total)
    return dict(q=q,n=n,enumerated_pairs=len(matrices)**2,full_frames=full_frames,
                checked_projection_gram_pairs=checks, distinct_gram_matrices=len(gram_totals),
                totals_by_gram_rank={str(k):sorted(v) for k,v in by_rank.items()},passed=True)

if __name__ == '__main__':
    results=[check(2,2),check(3,2),check(2,3)]
    target=Path(__file__).resolve().parents[1]/'results'/'exhaustive_check.json'
    target.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
