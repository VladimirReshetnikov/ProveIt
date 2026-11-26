#!/usr/bin/env python3
"""Exact finite checks of the split-orthogonal block comparison.

No third-party packages required.  All finite fields in this check are F_3.
Enumerate maximal isotropic subspaces by RREF and all square matrices for
m=1,2,3.  Independently enumerate SO^+(2m,3) for m=1,2 from elementary
generators and inspect every lower-left block.
"""
import itertools
import json
from collections import Counter, deque
from fractions import Fraction
from math import prod
from pathlib import Path


def rank(a, q):
    a = [list(row) for row in a]
    if not a:
        return 0
    r = 0
    for c in range(len(a[0])):
        p = next((i for i in range(r, len(a)) if a[i][c] % q), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        inv = pow(a[r][c], -1, q)
        a[r] = [(x * inv) % q for x in a[r]]
        for i in range(len(a)):
            if i != r:
                z = a[i][c]
                a[i] = [(x - z*y) % q for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def rref_subspaces(n, k, q):
    for pivots in itertools.combinations(range(n), k):
        nonpivots = set(range(n)) - set(pivots)
        positions = [(i, j) for i, p in enumerate(pivots)
                     for j in range(p + 1, n) if j in nonpivots]
        for values in itertools.product(range(q), repeat=len(positions)):
            a = [[0] * n for _ in range(k)]
            for i, p in enumerate(pivots):
                a[i][p] = 1
            for (i, j), v in zip(positions, values):
                a[i][j] = v
            yield a


def gaussian(n, k, q):
    if k < 0 or k > n:
        return 0
    result = Fraction(prod(q**n-q**i for i in range(k)),
                      prod(q**k-q**i for i in range(k)))
    assert result.denominator == 1
    return result.numerator


def mmul(a, b, q):
    n = len(a)
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(n)) % q
                       for j in range(n)) for i in range(n))


def transpose(a):
    return tuple(zip(*a))


def identity(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def inverse(a, q):
    n = len(a)
    rows = [list(a[i]) + list(identity(n)[i]) for i in range(n)]
    for c in range(n):
        p = next(i for i in range(c, n) if rows[i][c])
        rows[p], rows[c] = rows[c], rows[p]
        v = pow(rows[c][c], -1, q)
        rows[c] = [(x*v) % q for x in rows[c]]
        for i in range(n):
            if i != c:
                v = rows[i][c]
                rows[i] = [(x-v*y) % q for x,y in zip(rows[i], rows[c])]
    return tuple(tuple(row[n:]) for row in rows)


def block(a, b, c, d):
    return tuple(tuple(x)+tuple(y) for x,y in zip(a,b)) + \
        tuple(tuple(x)+tuple(y) for x,y in zip(c,d))


def so_elements(m, q):
    eye = identity(m)
    zero = tuple((0,) * m for _ in range(m))
    generators = []
    p = [list(row) for row in eye]
    p[0][0] = q-1
    generators.append(block(p,zero,zero,transpose(inverse(p,q))))
    for i in range(m):
        for j in range(m):
            if i == j:
                continue
            p = [list(row) for row in eye]
            p[i][j] = 1
            generators.append(block(p,zero,zero,transpose(inverse(p,q))))
    for i in range(m):
        for j in range(i+1,m):
            s = [[0]*m for _ in range(m)]
            s[i][j], s[j][i] = 1, q-1
            generators.append(block(eye,s,zero,eye))
            generators.append(block(eye,zero,s,eye))
    first = identity(2*m)
    seen, queue = {first}, deque([first])
    while queue:
        g = queue.popleft()
        for h in generators:
            gh = mmul(g,h,q)
            if gh not in seen:
                seen.add(gh)
                queue.append(gh)
    expected = q**(m*(m-1))*(q**m-1)*prod(q**(2*i)-1 for i in range(1,m))
    assert len(seen) == expected
    jform = block(zero,eye,eye,zero)
    assert all(mmul(mmul(transpose(g),jform,q),g,q) == jform for g in seen)
    return seen


def main():
    q, results = 3, []
    for m in range(1,4):
        iso_counts, total_subspaces = Counter(), 0
        for a in rref_subspaces(2*m,m,q):
            total_subspaces += 1
            if all(sum(a[i][k]*a[j][k+m]+a[i][k+m]*a[j][k]
                       for k in range(m)) % q == 0
                   for i in range(m) for j in range(m)):
                iso_counts[rank([row[m:] for row in a],q)] += 1
        assert total_subspaces == gaussian(2*m,m,q)
        total_iso = 2*prod(1+q**i for i in range(1,m))
        assert sum(iso_counts.values()) == total_iso
        for r in range(m+1):
            assert iso_counts[r] == gaussian(m,r,q)*q**(r*(r-1)//2)
        all_counts = Counter()
        for entries in itertools.product(range(q),repeat=m*m):
            a = [entries[i*m:(i+1)*m] for i in range(m)]
            all_counts[rank(a,q)] += 1
        total_matrix = q**(m*m)
        for r in range(m+1):
            assert all_counts[r] == gaussian(m,r,q)*prod(q**m-q**i for i in range(r))
        unif = [Fraction(all_counts[r],total_matrix) for r in range(m+1)]
        full = [Fraction(iso_counts[r],total_iso) for r in range(m+1)]
        special = [2*full[r] if r % 2 == 0 else Fraction(0) for r in range(m+1)]
        assert sum(special) == 1
        assert all(special[r] >= unif[r] for r in range(0,m+1,2))
        tvso = sum(abs(special[r]-unif[r]) for r in range(m+1))/2
        tvo = sum(abs(full[r]-unif[r]) for r in range(m+1))/2
        assert tvso == sum(unif[r] for r in range(1,m+1,2))
        assert tvo == unif[m]-full[m]
        group_size = None
        if m <= 2:
            group = so_elements(m,q)
            group_size = len(group)
            blocks = Counter(tuple(g[i][j] for i in range(m,2*m) for j in range(m)) for g in group)
            by_rank = {}
            for entries in itertools.product(range(q),repeat=m*m):
                r = rank([entries[i*m:(i+1)*m] for i in range(m)],q)
                count = blocks[entries]
                if r in by_rank:
                    assert by_rank[r] == count
                else:
                    by_rank[r] = count
                assert Fraction(count,group_size)*all_counts[r] == special[r]
        results.append({
            'q':q,'m':m,'rref_subspaces_enumerated':total_subspaces,
            'maximal_isotropic_subspaces':total_iso,
            'isotropic_subspaces_by_block_rank':dict(iso_counts),
            'iid_matrices_by_rank':dict(all_counts),
            'SO_rank_probabilities':[str(x) for x in special],
            'O_rank_probabilities':[str(x) for x in full],
            'iid_rank_probabilities':[str(x) for x in unif],
            'TV_SO_exact':str(tvso),'TV_O_exact':str(tvo),
            'SO_elements_independently_enumerated':group_size})
    path = Path(__file__).resolve().parents[1] / 'checks' / 'orthogonal_blocks_checks.json'
    path.write_text(json.dumps({'status':'all exact checks passed','results':results},indent=2)+'\n')
    print(path.read_text())


if __name__ == '__main__':
    main()
