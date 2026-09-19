#!/usr/bin/env python3
"""Exact coefficients for A_l(x)=x exp(A_l^{compose l}(x)).

Python 3.10+, standard library only.  All modular recurrences are division-free.
Arrays include a[0]=0.  Iteration zero means the identity series x.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import product
from math import factorial
import heapq


def coefficients(ell: int, nmax: int, modulus: int | None = None) -> list[int]:
    """Return a_l(0),...,a_l(nmax) using incremental partial Bell polynomials.

    Cost: O(nmax^3 + ell*nmax^2) integer/ring operations;
    memory O(nmax^2 + ell*nmax). This is not a bit-complexity bound.
    No parameter reduction is applied, so tests of parameter periodicity are
    independent of that theorem.
    """
    if not isinstance(ell, int) or ell < 0:
        raise ValueError("ell must be a nonnegative integer")
    if not isinstance(nmax, int) or nmax < 0:
        raise ValueError("nmax must be a nonnegative integer")
    if modulus is not None and (not isinstance(modulus, int) or modulus < 2):
        raise ValueError("modulus must be None or an integer >= 2")
    if nmax == 0:
        return [0]
    choose = [[1]]
    for n in range(1, nmax + 1):
        row = [1] + [choose[-1][j-1] + choose[-1][j] for j in range(1,n)] + [1]
        choose.append(row if modulus is None else [x % modulus for x in row])
    a = [0] * (nmax + 1)
    a[1] = 1
    it = [[0] * (nmax + 1) for _ in range(max(ell, 1) + 1)]
    bell = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    bell[0][0] = 1
    expc = [0] * (nmax + 1)
    expc[0] = 1
    for n in range(1, nmax + 1):
        it[0][n] = int(n == 1)
        it[1][n] = a[n]
        for k in range(1, n + 1):
            value = sum(choose[n-1][j-1] * a[j] * bell[n-j][k-1]
                        for j in range(1, n-k+2))
            bell[n][k] = value if modulus is None else value % modulus
        for k in range(2, ell + 1):
            value = sum(it[k-1][j] * bell[n][j] for j in range(1,n+1))
            it[k][n] = value if modulus is None else value % modulus
        value = sum(choose[n-1][j-1] * it[ell][j] * expc[n-j]
                    for j in range(1,n+1))
        expc[n] = value if modulus is None else value % modulus
        if n < nmax:
            a[n+1] = (n+1) * expc[n]
            if modulus is not None:
                a[n+1] %= modulus
    return a


def rational_fixed_point(ell: int, nmax: int) -> list[int]:
    """Independent OGF implementation with exact Fraction arithmetic.

    Iterates the original functional equation, with ordinary convolution,
    Horner composition, and E'=H'E for the exponential. Intended for small N.
    """
    if ell < 0 or nmax < 1:
        raise ValueError("ell >= 0 and nmax >= 1 are required")
    z = [Fraction(0)] * (nmax+1)
    z[1] = Fraction(1)
    def mul(a, b):
        out = [Fraction(0)] * (nmax+1)
        for i, ai in enumerate(a):
            if ai:
                for j in range(nmax+1-i):
                    if b[j]: out[i+j] += ai*b[j]
        return out
    def compose(a, b):
        out = [Fraction(0)] * (nmax+1)
        for ai in reversed(a):
            out = mul(out,b)
            out[0] += ai
        return out
    def exp_zero(h):
        assert h[0] == 0
        out = [Fraction(0)] * (nmax+1)
        out[0] = Fraction(1)
        for n in range(1,nmax+1):
            out[n] = sum(j*h[j]*out[n-j] for j in range(1,n+1))/n
        return out
    a = z[:]
    for _ in range(nmax):
        h = z[:]
        for _ in range(ell): h = compose(a,h)
        e = exp_zero(h)
        a = [Fraction(0)] + e[:-1]
    result = [a[n]*factorial(n) for n in range(nmax+1)]
    if any(x.denominator != 1 for x in result):
        raise ArithmeticError("Nonintegral EGF coefficient")
    return [x.numerator for x in result]


def small_core_weights(ell: int, r: int) -> Counter[int]:
    """Exact distribution of total vertex type for cores of sizes 1,...,4.

    Uses the four rooted unlabelled tree shapes of size four, with their
    labelled multiplicities. Counter keys are total type S, not residues.
    """
    if ell < 0 or r not in (1,2,3,4):
        raise ValueError("ell >= 0 and 1 <= r <= 4 are required")
    out: Counter[int] = Counter()
    if r == 1: out[1] += 1
    elif r == 2: out[1+ell] += 2
    elif r == 3:
        out[1+2*ell] += 3
        for t in range(ell,2*ell): out[1+ell+t] += 6
    else:
        out[1+3*ell] += 4
        for t in range(ell,2*ell):
            out[1+2*ell+t] += 24
            for s in range(ell,2*ell): out[1+ell+s+t] += 12
            for u in range(ell,ell+t): out[1+ell+t+u] += 24
    return out


def prufer_core_weights(ell: int, r: int) -> Counter[int]:
    """Independent labelled-tree and type enumeration, suitable for r <= 5.

    Every unrooted labelled tree is obtained from its Pruefer code; every
    choice of root is then used. Child types are enumerated directly.
    """
    if ell < 0 or not 1 <= r <= 5:
        raise ValueError("ell >= 0 and 1 <= r <= 5 are required")
    if r == 1: return Counter({1:1})
    result: Counter[int] = Counter()
    for code in product(range(r),repeat=r-2):
        deg = [1]*r
        for v in code: deg[v] += 1
        leaves = [v for v in range(r) if deg[v] == 1]
        heapq.heapify(leaves)
        adj = [[] for _ in range(r)]
        for v in code:
            u = heapq.heappop(leaves)
            adj[u].append(v); adj[v].append(u)
            deg[u] -= 1; deg[v] -= 1
            if deg[v] == 1: heapq.heappush(leaves,v)
        u,v = leaves
        adj[u].append(v); adj[v].append(u)
        for root in range(r):
            parent = [-1]*r
            order = [root]
            for v in order:
                for u in adj[v]:
                    if u != parent[v]:
                        parent[u] = v; order.append(u)
            types = [0]*r
            types[root] = 1
            def visit(i: int, total: int):
                if i == r:
                    result[total] += 1
                    return
                v = order[i]
                for t in range(ell, ell+types[parent[v]]):
                    types[v] = t
                    visit(i+1,total+t)
            visit(1,1)
    return result


def predicted_mod3(ell: int, n: int) -> int:
    if n < 1: return 0
    q,r = divmod(n,3)
    return 0 if r == 0 else 1 if r == 1 else 2*pow(ell+1,q,3)%3


def predicted_mod4(ell: int, n: int) -> int:
    if n < 1: return 0
    q,r = divmod(n,4)
    if r == 0: return 0
    if r == 1: return 1
    if r == 2: return 2*pow(ell+1,2*q,4)%4
    return (3+2*ell)%4 if q == 0 else (3+2*((ell+1)//2))%4


def predicted_multiple5(h: int, n: int) -> int:
    """Closed formula for a_{5h}(n) modulo 5."""
    if n >= 23 and n % 20 == 3: return (3-h)%5
    if n >= 24 and n % 20 == 4: return (4-2*h)%5
    return n%5


def core_residue(weights: Counter[int], q: int, p: int, alpha: int = 1) -> int:
    """Evaluate sum_T S(T)^(p^(alpha-1)*q) modulo p^alpha."""
    m = p**alpha
    d = p**(alpha-1)*q
    return sum(count*pow(s,d,m) for s,count in weights.items())%m

if __name__ == '__main__':
    import argparse, json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('ell',type=int)
    parser.add_argument('nmax',type=int)
    parser.add_argument('--modulus',type=int)
    args = parser.parse_args()
    print(json.dumps(coefficients(args.ell,args.nmax,args.modulus)))
