"""Independent finite-group join-matrix audit (no production cut rows).

Enumerates genuine gain partitions, computes common-extension connectivity,
checks the integer zeta-diagonal factorization, and computes modular ranks.
The S3 case uses a noncommutative multiplication table.
"""
from __future__ import annotations
from itertools import product, permutations
from math import factorial
import json
from pathlib import Path


def cyclic(q):
    return [[(a+b)%q for b in range(q)] for a in range(q)]


def symmetric3():
    elems = list(permutations(range(3)))
    return [[elems.index(tuple(a[b[i]] for i in range(3))) for b in elems] for a in elems]


def set_partitions(r):
    def rec(labels, blocks):
        if len(labels) == r:
            yield tuple(labels); return
        for k in range(blocks+1):
            yield from rec(labels+[k], max(blocks,k+1))
    yield from rec([0],1)


def gain_states(r,q):
    for labels in set_partitions(r):
        first = {labels.index(k) for k in set(labels)}
        free = [i for i in range(r) if i not in first]
        for values in product(range(q),repeat=len(free)):
            offsets = [0]*r
            for i,a in zip(free,values): offsets[i] = a
            yield labels, tuple(offsets)


def rank_mod(matrix,p):
    a = [[x%p for x in row] for row in matrix]
    rank = 0
    for c in range(len(a[0]) if a else 0):
        pivot = next((i for i in range(rank,len(a)) if a[i][c]),None)
        if pivot is None: continue
        a[rank],a[pivot] = a[pivot],a[rank]
        inv = pow(a[rank][c],-1,p)
        a[rank] = [(x*inv)%p for x in a[rank]]
        for i in range(rank+1,len(a)):
            if a[i][c]:
                factor = a[i][c]
                a[i] = [(x-factor*y)%p for x,y in zip(a[i],a[rank])]
        rank += 1
        if rank == len(a): break
    return rank


def bareiss_det(matrix):
    a = [row[:] for row in matrix]; sign = 1; previous = 1; n = len(a)
    for k in range(n-1):
        pivot = next((i for i in range(k,n) if a[i][k]),None)
        if pivot is None: return 0
        if pivot != k:
            a[k],a[pivot] = a[pivot],a[k]; sign *= -1
        d = a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator = a[i][j]*d - a[i][k]*a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = d
    return sign*a[-1][-1] if n else 1


def audit_case(name,mult,r):
    q = len(mult); inv = [next(b for b in range(q) if mult[a][b] == 0 and mult[b][a] == 0) for a in range(q)]
    states = list(gain_states(r,q)); n = len(states)
    def relative(s,i,j): return mult[inv[s[1][i]]][s[1][j]]
    def extends(a,b):
        return all(a[0][i] != a[0][j] or (b[0][i] == b[0][j] and relative(a,i,j) == relative(b,i,j))
                   for i in range(r) for j in range(i))
    zeta = [[int(extends(a,b)) for b in states] for a in states]
    diag = [(-q)**max(s[0])*factorial(max(s[0])) for s in states]
    all_values = [(0,)+a for a in product(range(q),repeat=r-1)]
    solutions = []
    for s in states:
        solutions.append({a for a in all_values if all(s[0][i] != s[0][j] or
                         a[j] == mult[a[i]][relative(s,i,j)] for i in range(r) for j in range(r))})
    def connected(a,b):
        reached = {0}
        while True:
            nxt = reached | {j for i in reached for j in range(r)
                             if a[0][i] == a[0][j] or b[0][i] == b[0][j]}
            if nxt == reached: return len(reached) == r
            reached = nxt
    kernel = [[int(bool(solutions[i]&solutions[j]) and connected(a,b)) for j,b in enumerate(states)] for i,a in enumerate(states)]
    entries = 0
    for i in range(n):
        for j in range(n):
            assert sum(zeta[i][k]*diag[k]*zeta[j][k] for k in range(n)) == kernel[i][j]
            entries += 1
    determinant = bareiss_det(kernel)
    expected = 1
    for x in diag: expected *= x
    assert determinant == expected != 0
    ranks = {}
    for p in (2,3,5,7):
        observed = rank_mod(kernel,p); predicted = sum(x%p != 0 for x in diag)
        assert observed == predicted
        ranks[str(p)] = observed
    return {"group":name,"order":q,"ports":r,"states":n,"factorization_entries":entries,
            "rank_mod":ranks,"determinant_hex":hex(determinant),"determinant_bits":abs(determinant).bit_length()}


def run():
    return [audit_case(name,mult,r) for name,mult,r in
            [("trivial",cyclic(1),5),("C2",cyclic(2),4),("C3",cyclic(3),3),("S3",symmetric3(),3)]]

if __name__ == "__main__":
    data = run()
    print(json.dumps(data,indent=2))
