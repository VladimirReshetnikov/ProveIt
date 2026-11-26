#!/usr/bin/env python3
"""Exact numerical checks for the rank-two onset theorem. Standard Python 3."""
from collections import defaultdict
from itertools import combinations
from math import comb, gcd


def vp(n, p):
    if not n:
        raise ValueError("valuation of zero")
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def ceil_log(n, p):
    k, bound = 0, 1
    while bound < n:
        k += 1
        bound *= p
    return k


def cyclotomic_residue(f, a, b, p, h):
    """Remainder in Z[X] after substitution into the primitive cyclotomic ring."""
    size = p**h
    block = size // p
    degree = size - block
    result = defaultdict(int)
    for (u, v), c in f.items():
        n = (a*u + b*v) % size
        if n < degree:
            result[n] += c
        else:
            for i in range(p-1):
                result[n-degree+i*block] -= c
    return {j: c for j, c in result.items() if c}


def first_nonzero(terms, p, block):
    """Order of the sparse polynomial modulo p at 1; block is a power of p."""
    while block:
        # Write X=1+T and X^block=1+T^block in characteristic p.
        # Scan only the first nonzero block of coefficients in the shifted basis.
        for t in range(p):
            row = defaultdict(int)
            for j, c in terms.items():
                hi, lo = divmod(j, block)
                if hi >= t:
                    row[lo] += c*comb(hi, t)
            row = {j: c % p for j, c in row.items() if c % p}
            if row:
                if block == 1:
                    return t
                return t*block + first_nonzero(row, p, block//p)
        raise AssertionError("zero shift of nonzero polynomial")
    raise ValueError("invalid block size")


def local(f, a, b, p, h):
    coeff = cyclotomic_residue(f, a, b, p, h)
    if not coeff:
        raise ValueError("nontrivial torsion zero")
    common = min(vp(c, p) for c in coeff.values())
    terms = {j: c // p**common % p for j, c in coeff.items()
             if c // p**common % p}
    block = p**(h-1)
    return (p-1)*block*common + first_nonzero(terms, p, block)


def shell(f, p, h):
    n = p**h
    return (sum(local(f, 1, b, p, h) for b in range(n))
            + sum(local(f, a, 1, p, h) for a in range(0, n, p)))


def bareiss(matrix):
    if len(matrix) == 1:
        return matrix[0][0]
    a = [row.copy() for row in matrix]
    previous = 1
    sign = 1
    for k in range(len(a)-1):
        if not a[k][k]:
            pivot = next((i for i in range(k+1,len(a)) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign *= -1
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                n = a[i][j]*a[k][k] - a[i][k]*a[k][j]
                a[i][j], rem = divmod(n, previous)
                assert rem == 0
        previous = a[k][k]
    return sign*a[-1][-1]


def independent_norm(f, a, b, p, h):
    """Integer determinant of multiplication by F in Z[X]/Phi. No Taylor orders."""
    n = p**h
    block = n//p
    e = n-block
    columns = []
    for j in range(e):
        vec = [0]*n
        for (u,v), c in f.items():
            vec[(a*u+b*v+j) % n] += c
        for t in range(e,n):
            for k in range(p-1):
                vec[t-e+k*block] -= vec[t]
        columns.append(vec[:e])
    return vp(bareiss(columns), p)


def bouquet(steps):
    coeff = defaultdict(int)
    for a,b,c in steps:
        coeff[0,0] += 2*c
        coeff[a,b] -= c
        coeff[-a,-b] -= c
    return {key: val for key, val in coeff.items() if val}


def check_shell_law(name, p, f):
    height = max(max(abs(a), abs(b)) for a,b in f)
    onset = ceil_log(8*height**2+1,p) + ceil_log(2*height+1,p) + 2
    for h in range(1,4):
        n = p**h
        if n-n//p > 8:
            break
        for a,b in [(1,t) for t in range(n)] + [(t,1) for t in range(0,n,p)]:
            assert local(f,a,b,p,h) == independent_norm(f,a,b,p,h)
    data = [shell(f,p,h) for h in range(onset, onset+6)]
    differences = data
    for base in (1,p,p,p*p):
        differences = [b-base*a for a,b in zip(differences, differences[1:])]
    assert differences == [0, 0], (name, data, differences)
    print(f"{name}: p={p}, H={height}, h={onset}..{onset+5}, shells={data}", flush=True)



def vanishing_slopes(poly, p):
    """All primitive projection directions giving the zero Laurent polynomial mod p."""
    support = [a for a,c in poly.items() if c % p]
    candidates = set()
    for (a,b),(x,y) in combinations(support,2):
        u,v = b-y, x-a
        g = gcd(u,v)
        u,v = u//g,v//g
        if u < 0 or (u == 0 and v < 0):
            u,v = -u,-v
        candidates.add((u,v))
    zeros = set()
    for u,v in candidates:
        coeff = defaultdict(int)
        for (a,b),c in poly.items():
            coeff[a*u+b*v] += c
        if all(c % p == 0 for c in coeff.values()):
            zeros.add((u,v))
    return sorted(zeros)


def check_thresholds():
    for p in (2,3,5,7,11):
        def steps(delta):
            if p == 2:
                return [(1,0,1),(1,1,1),(delta,1+2*delta,1)]
            return [(1,0,p-2),(1,1,1),(1+delta,2,1)]
        s = 2
        early, late = bouquet(steps(0)), bouquet(steps(p**s))
        before, after = vanishing_slopes(early,p), vanishing_slopes(late,p)
        assert before and not after
        for h in range(1,s+1):
            assert shell(early,p,h) == shell(late,p,h)
        print(f"m={max(p,3)}, p={p}: old vanishing directions={before}, new={after}")


def main():
    check_shell_law("weighted diagonal and horizontal", 2,
                    bouquet([(1,-1,1),(1,0,8)]))
    check_shell_law("ternary weighted grid with content", 3,
                    bouquet([(0,1,9),(1,0,27)]))
    # (Y-X)(Y-1)+2^6 is nonzero on the entire unit torus by magnitude.
    check_shell_law("two distinct exceptional slopes", 2,
                    {(0,2):1, (0,1):-1, (1,1):-1, (1,0):1, (0,0):64})
    for s in (2,3,4):
        f = bouquet([(3**s,0,1),(0,1,1),(1,0,3)])
        v, seq = 0, []
        for n in range(1, 7):
            v += shell(f,3,n)-2
            t = min(n,s)
            predicted = 2*t*3**n+4*(3**n-3**t)+3**t-1+2*t-2*n
            assert v == predicted
            seq.append(v)
        print(f"five-loop lower example s={s}: levels 1..6 = {seq}")
    check_thresholds()
    print("All exact checks passed.")


if __name__ == "__main__":
    main()
