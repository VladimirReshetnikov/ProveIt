#!/usr/bin/env python3
"""Exact checks. Uses integer cyclotomic reduction and fraction-free Laplacian cofactors."""
from itertools import product
from math import comb
from collections import Counter

SQUARE = ((1, 0), (0, 1))
DV3 = ((1, 5), (0, 3), (1, 2), (0, 1))
DV5 = ((1, 0), (2, 3), (1, 1))


def vp(value, prime):
    assert value
    total = 0
    while value % prime == 0:
        total += 1
        value //= prime
    return total


def directions(p, h, d):
    """Unit-scaling orbits, with first unit normalized to 1."""
    q = p**h
    for pivot in range(d):
        ranges = [range(0, q, p)] * pivot + [(1,)] + [range(q)] * (d - pivot - 1)
        yield from product(*ranges)


def projections(direction, steps):
    return [sum(a*b for a, b in zip(direction, step)) for step in steps]


def sparse_eigenvalue(q, powers):
    poly = Counter({0: 2*len(powers)})
    for k in powers:
        poly[k % q] -= 1
        poly[-k % q] -= 1
    return poly


def local_order(p, h, powers):
    q = p**h
    gap = q//p
    ram = q-gap
    poly = sparse_eigenvalue(q, powers)
    # Reduce modulo Phi_q(X) = 1 + X^gap + ... + X^ram.
    for k in list(poly):
        if k >= ram:
            high = poly.pop(k)
            for j in range(p-1):
                poly[k-ram+j*gap] -= high
    poly = {k: c for k, c in poly.items() if c}
    # Expand X = 1+T. The valuations of nonzero terms with j<ram are
    # distinct modulo ram, so the minimum is exact. Stop when j bounds it.
    best = None
    for j in range(ram):
        if best is not None and j >= best:
            break
        c = sum(c*comb(k,j) for k,c in poly.items() if j <= k)
        if c:
            value = j + ram*vp(c,p)
            best = value if best is None else min(best, value)
    assert best is not None
    return best


def mod_symbol_order(p, modulus, powers):
    poly = sparse_eigenvalue(modulus, powers)
    return next(j for j in range(modulus)
                if sum(c*comb(k,j) for k,c in poly.items() if j <= k) % p)


def shell(p, h, steps):
    return sum(local_order(p,h,projections(u,steps))
               for u in directions(p,h,len(steps[0])))


def cofactor(p, n, steps):
    q = p**n
    d = len(steps[0])
    vertices = list(product(range(q), repeat=d))
    indices = {v:i for i,v in enumerate(vertices)}
    size = len(vertices)-1
    matrix = [[0]*size for _ in range(size)]
    for i,v in enumerate(vertices[:-1]):
        matrix[i][i] += 2*len(steps)
        for step in steps:
            for sign in (-1,1):
                w = tuple((x+sign*t)%q for x,t in zip(v,step))
                j = indices[w]
                if j < size:
                    matrix[i][j] -= 1
    # Leading principal minors are positive in a connected reduced Laplacian.
    previous = 1
    for k in range(size-1):
        pivot = matrix[k][k]
        assert pivot > 0
        for i in range(k+1, size):
            for j in range(k+1,size):
                a = pivot*matrix[i][j] - matrix[i][k]*matrix[k][j]
                quotient, remainder = divmod(a,previous)
                assert remainder == 0
                matrix[i][j] = quotient
        previous = pivot
    return matrix[-1][-1]


def first_moment(p, powers):
    for r in range(1,len(powers)+1):
        if sum(pow(a,2*r,p) for a in powers) % p:
            return 2*r
    raise ValueError("No nonzero moment in the specified range")


def dv_predictions(example,n):
    q = (2 if example <= 3 else 3)**n
    if example == 1:
        return (2*n+4)*q-6*n-1
    if example == 2:
        return (2*n+4)*q-6*n-1 + q*q-1
    if example == 3:
        return (5,19,65)[n-1] if n<=3 else n*q+33*q//4-4*n-1
    if example == 4:
        return 4*q-2*n-4
    return 20*(q//3)-2*n-8


def main():
    cases = [(2,SQUARE,10),(2,SQUARE*2,10),(2,DV3,10),(3,SQUARE,7),(3,DV5,7)]
    for e,(p,steps,upto) in enumerate(cases,1):
        accum = 0
        values = []
        for n in range(1,upto+1):
            accum += shell(p,n,steps)
            exact = accum-2*n
            assert exact == dv_predictions(e,n)
            if p**(2*n) <= 90:
                assert vp(cofactor(p,n,steps),p) == exact
            values.append(exact)
        print(f"DuBose–Vallières {e}: {values}")
    print("Example 5 mod-9 orbit orders:",
          [(u,mod_symbol_order(3,9,projections(u,DV5))) for u in directions(3,2,2)])
    for p,steps,levels in [
        (5,SQUARE,3),(7,SQUARE,2),(7,((1,1),(3,5),(2,4)),2),
        (7,((1,0,0),(0,1,0),(0,0,1)),2),
        (11,((1,0),(2,3),(4,2),(1,7)),2),
        (13,((1,1),(2,7),(4,10),(8,5),(3,9),(6,11)),2),
    ]:
        d = len(steps[0])
        coeff = sum(first_moment(p,projections(u,steps)) for u in directions(p,1,d))
        for h in range(1,levels+1):
            assert shell(p,h,steps) == coeff*p**((h-1)*(d-1))
        print(f"Moment test: p={p}, d={d}, m={len(steps)}, A={coeff}, h=1..{levels}")
    print("All integer checks passed.")


if __name__ == "__main__":
    main()
