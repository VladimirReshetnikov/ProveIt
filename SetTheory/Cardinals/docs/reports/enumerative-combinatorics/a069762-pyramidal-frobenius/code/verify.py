#!/usr/bin/env python3
"""Exact checks and algorithms accompanying the A069762 research report.

Python 3.10+; SymPy is needed only for --symbolic. No network access is used.
Finite tests supplement, rather than replace, the proofs in article.tex.
"""
from __future__ import annotations
import argparse
import csv
from dataclasses import dataclass
from fractions import Fraction
from heapq import heappop, heappush
from math import comb, gcd
from pathlib import Path
import random
import time

K = (1, 2, 3, 2, 1, 6)
H = (0, 3, 2, 3, 0, 5)
CORRECTIONS = {2: 10, 3: 40, 5: 315, 11: 1612, 17: 3135, 23: 2400}
D = (1, 2, -1, -8, -9, 6, 23, 16, -14, -32,
     -14, 16, 23, 6, -9, -8, -1, 2, 1)
OEIS = (51, 191, 609, 1324, 2813, 4711, 8576, 13894, 23319,
        34165, 51661, 71126, 100529, 136239, 187543, 241586,
        321251, 404839, 516704, 645358, 813141, 982651, 1221299,
        1463734, 1767473, 2106271, 2524101, 2940909, 3500209,
        4061663, 4736456, 5474526, 6352219, 7228469)

def pyr(n: int) -> int:
    if n < 0:
        raise ValueError('n must be nonnegative')
    return n * (n + 1) * (2 * n + 1) // 6

@dataclass(frozen=True)
class Parameters:
    n: int
    a: int
    b: int
    c: int
    k: int
    ell: int
    d: int
    e: int
    A: int
    B: int
    C: int

def parameters(n: int) -> Parameters:
    if not isinstance(n, int) or n < 2:
        raise ValueError('n must be an integer at least 2')
    a, b, c = pyr(n), pyr(n + 1), pyr(n + 2)
    k, ell = gcd(n + 1, 6), gcd(n + 2, 6)
    d, e = (n + 1) // k, (n + 2) // ell
    return Parameters(n, a, b, c, k, ell, d, e, a // d,
                      b // (d * e), c // e)

def frobenius(n: int) -> int:
    """Proved all-n formula, using integer arithmetic only."""
    if n < 2:
        raise ValueError('n must be at least 2')
    h = H[n % 6]
    num = (4*n**5 + 32*n**4 + (101-10*h)*n**3
           + (175-45*h)*n**2 + (102-65*h)*n - 36-30*h)
    q, rem = divmod(num, 36)
    if rem:
        raise ArithmeticError('nonintegral formula value')
    return q + CORRECTIONS.get(n, 0)


def inverse_index(y: int) -> int | None:
    """Largest n>=2 with F_n<=y, by exact monotone binary search."""
    if y < frobenius(2):
        return None
    low, high = 2, 4
    while frobenius(high) <= y:
        low, high = high, 2*high
    while high-low > 1:
        middle = (low+high)//2
        if frobenius(middle) <= y:
            low = middle
        else:
            high = middle
    return low

def genus(n: int) -> int:
    """Exact genus; unlike the Frobenius formula, no exceptions occur."""
    if n < 2:
        raise ValueError('n must be at least 2')
    j = (0, 9, 8, 9, 0, 5)[n % 6]
    num = (n*(n+1)*(4*n**3+28*n**2+73*n+102)
           - 5*j*(n+1)*(n+2))
    q, rem = divmod(num, 72)
    if rem:
        raise ArithmeticError('nonintegral genus value')
    return q

def l_representatives(p: Parameters) -> list[int]:
    ls = list(range(p.B))
    if p.n % 6 in (1, 2):
        ls.remove(1)
        ls.append(p.B + 1)
    return ls

def reduced_weight(p: Parameters, L: int) -> tuple[int, int, int]:
    v = 0 if p.k == 1 else (L * pow(p.ell, -1, p.k)) % p.k
    u = (L - p.ell*v) // p.k
    return p.A*u + p.C*v, u, v

def reduced_apery(n: int) -> list[int]:
    p = parameters(n)
    out = [-1] * p.B
    for L in l_representatives(p):
        w, u, v = reduced_weight(p, L)
        assert u >= 0 and v >= 0 and out[w % p.B] == -1
        out[w % p.B] = w
    return out

def lifted_apery(n: int) -> list[int]:
    """Apéry set w.r.t. b, indexed by residue; memory grows as O(n^3)."""
    p = parameters(n)
    out = [-1] * p.b
    for w in reduced_apery(n):
        for i in range(p.e):
            for j in range(p.d):
                W = p.d*p.e*w + i*p.a + j*p.c
                assert out[W % p.b] == -1
                out[W % p.b] = W
    return out

def representation(n: int, x: int) -> tuple[int, int, int] | None:
    """Find x=alpha*a+beta*b+gamma*c, or certify that x is a gap.

    Uses a bounded number of exact arithmetic operations and modular inverses,
    not a search through the Apéry set. All n>=2 and all integers x are allowed.
    """
    p = parameters(n)
    if x < 0:
        return None
    j = 0 if p.d == 1 else (x * pow(p.c, -1, p.d)) % p.d
    y = (x - j*p.c) // p.d
    i = 0 if p.e == 1 else (y * pow(p.A, -1, p.e)) % p.e
    z = (y - i*p.A) // p.e
    L = (2*z) % p.B
    if p.n % 6 in (1, 2) and L == 1:
        L = p.B + 1
    w, u, v = reduced_weight(p, L)
    if z < w:
        return None
    t, rem = divmod(z-w, p.B)
    assert rem == 0
    ans = (i+p.e*u, t, j+p.d*v)
    assert all(c >= 0 for c in ans)
    assert ans[0]*p.a+ans[1]*p.b+ans[2]*p.c == x
    return ans

def dijkstra_apery(gens: tuple[int, ...], modulus: int) -> list[int]:
    """Independent shortest-path algorithm, valid for modulus in the semigroup."""
    if modulus <= 0 or any(g <= 0 for g in gens):
        raise ValueError('positive generators and modulus required')
    if gcd(modulus, gcd(*gens)) != 1:
        raise ValueError('generators and modulus must have gcd 1')
    dist: list[int | None] = [None] * modulus
    dist[0] = 0
    heap = [(0, 0)]
    while heap:
        distance, r = heappop(heap)
        if dist[r] != distance:
            continue
        for g in gens:
            rr, dd = (r + g) % modulus, distance + g
            if dist[rr] is None or dd < dist[rr]:
                dist[rr] = dd
                heappush(heap, (dd, rr))
    if any(v is None for v in dist):
        raise ArithmeticError('unreachable residue')
    return [int(v) for v in dist]

def invariant_pair(ap: list[int]) -> tuple[int, int]:
    m = len(ap)
    g = Fraction(sum(ap), m) - Fraction(m-1, 2)
    assert g.denominator == 1
    return max(ap)-m, int(g)

def gap_moment(ap: list[int], p: int) -> int:
    """Bernoulli formula for p=0,1,2,3 (the proof covers every p)."""
    if not 0 <= p <= 3:
        raise ValueError('this dependency-free implementation supports p<=3')
    bs = [Fraction(1), Fraction(-1, 2), Fraction(1, 6),
          Fraction(0), Fraction(-1, 30)]
    m = len(ap)
    total = Fraction(0)
    for j in range(p+2):
        total += (comb(p+1, j)*bs[j]*Fraction(m)**(j-1)
                  *sum(w**(p+1-j) for w in ap))
    total = (total-bs[p+1])/(p+1)
    assert total.denominator == 1
    return int(total)

def brute_gaps(n: int) -> list[int]:
    p = parameters(n)
    # The endpoint is found independently by Dijkstra, not by the new formula.
    F = max(dijkstra_apery((p.a, p.b, p.c), p.a))-p.a
    representable = bytearray(F+1)
    representable[0] = 1
    for t in range(1, F+1):
        representable[t] = any(t >= g and representable[t-g]
                               for g in (p.a, p.b, p.c))
    return [t for t in range(1, F+1) if not representable[t]]

def symbolic_checks() -> None:
    try:
        import sympy as sp
    except ImportError as exc:
        raise SystemExit('Install sympy to run --symbolic') from exc
    n, q, x, z, h = sp.symbols('n q x z h')
    P0 = (4*n**5+32*n**4+101*n**3+175*n**2+102*n-36)/36
    P = [sp.expand(P0-5*H[r]*(n+1)*(n+2)*(2*n+3)/36)
         for r in range(6)]
    for r in range(6):
        k, ell = K[r], K[(r+1)%6]
        d, e = (n+1)/k, (n+2)/ell
        a, c = n*(n+1)*(2*n+1)/6, (n+2)*(n+3)*(2*n+5)/6
        A, B, C = k*n*(2*n+1)/6, sp.Rational(k*ell,6)*(2*n+3), ell*(n+3)*(2*n+5)/6
        assert sp.expand(k*C-ell*A-5*B) == 0
        assert sp.expand(2*A-k-B*2*(n-1)/ell) == 0
        assert sp.expand(2*C-ell-B*2*(n+4)/k) == 0
        M = (A*(B-1), A*(B+1)/2, A*(B-1)/3+C,
             A*(B-1)/2, A*(B-1), A*(B-1)/6)[r]
        assert sp.expand(d*e*(M-B)+(e-1)*a+(d-1)*c-P[r]) == 0
        V = (0, (B-3)/2, B-2, (B-1)/2, 0, 5*(B-1)/2)[r]
        eta = int(r in (1, 2))
        gr = A/k*((B-1)/2+eta)+5*sp.sympify(V)/k-(B-1)/2
        gn = sp.expand(d*e*gr+((e-1)*a+(d-1)*c-d*e+1)/2)
        expected = (n*(n+1)*(4*n**3+28*n**2+73*n+102)
                    -5*(0,9,8,9,0,5)[r]*(n+1)*(n+2))/72
        assert sp.expand(gn-expected) == 0
        diff = sp.Poly(sp.expand((P[(r+1)%6].subs(n,n+1)-P[r])
                                .subs(n,24+r+6*q)),q)
        assert all(coef > 0 for coef in diff.all_coeffs())
    den = sp.expand((1-x)**6*(1+x)**4*(1+x+x*x)**4)
    assert [den.coeff(x,j) for j in range(19)] == list(D)
    aa = [0,0]+[frobenius(i) for i in range(2,120)]
    nc = [sum(D[j]*aa[i-j] for j in range(min(i,18)+1)) for i in range(120)]
    assert nc[41] == 2400 and all(v == 0 for v in nc[42:])
    numerator = sum(v*x**i for i,v in enumerate(nc))
    assert sp.gcd(numerator,den) == 1
    # Independent coefficient extraction from Lagrange inversion.
    R = (1+8*z+(101-10*h)*z**2/4+(175-45*h)*z**3/4
         +(102-65*h)*z**4/4+(-36-30*h)*z**5/4)
    expected_cs = [(50*h+7)/100, -3*(25*h+149)/500,
                   (2500*h*h-400*h+37817)/10000,
                   -3*(6250*h*h+37125*h+17199)/250000]
    for j in range(1,5):
        val = -sp.expand(sp.series(R**sp.Rational(j,5),z,0,j+2)
                         .removeO()).coeff(z,j+1)/j
        assert sp.simplify(val-expected_cs[j-1]) == 0
    assert sp.Poly(R,z).degree() == 5  # c_(5j)=0 follows for every j>=1.
    print('PASS symbolic identities: reductions, genus, monotonicity, recurrence, inversion')

def run_checks(out_dir: Path, symbolic: bool = False) -> None:
    start = time.perf_counter()
    assert [frobenius(n) for n in range(2,36)] == list(OEIS)
    print('PASS all 34 displayed OEIS values, n=2..35')
    for n in range(2,1001):
        p = parameters(n)
        assert (p.d, p.e) == (gcd(p.a,p.b),gcd(p.b,p.c))
        assert gcd(p.d,p.e) == gcd(p.d,p.c) == gcd(p.e,p.A) == 1
        assert p.k*p.C-p.ell*p.A == 5*p.B
        assert (2*p.A-p.k) % p.B == (2*p.C-p.ell) % p.B == 0
        ap = reduced_apery(n)
        assert ap == dijkstra_apery((p.A,p.B,p.C),p.B)
        fr, gr = invariant_pair(ap)
        assert frobenius(n) == p.d*p.e*fr+(p.e-1)*p.a+(p.d-1)*p.c
        assert genus(n) == p.d*p.e*gr+Fraction((p.e-1)*p.a+(p.d-1)*p.c-p.d*p.e+1,2)
    print('PASS reduced Apéry sets and all invariants against Dijkstra, n=2..1000')
    for n in range(2,61):
        p = parameters(n)
        ap = dijkstra_apery((p.a,p.b,p.c),p.a)
        assert invariant_pair(ap) == (frobenius(n),genus(n))
    print('PASS original-generator Dijkstra (no gcd reduction), n=2..60')
    for n in range(2,31):
        p = parameters(n)
        assert lifted_apery(n) == dijkstra_apery((p.a,p.b,p.c),p.b)
    print('PASS full lifted Apéry sets against original generators, n=2..30')
    rng = random.Random(69762)
    for n in range(2,201):
        p = parameters(n)
        ap = dijkstra_apery((p.a,p.b,p.c),p.a) if n <= 30 else None
        points = [0,1,frobenius(n),frobenius(n)+1]
        points += [rng.randrange(0,2*frobenius(n)+1) for _ in range(30)]
        for xx in points:
            rep = representation(n,xx)
            if ap is not None:
                assert (rep is not None) == (xx >= ap[xx % p.a])
            if xx == frobenius(n): assert rep is None
            if xx > frobenius(n): assert rep is not None
    print('PASS constructive membership certificates and boundary checks, n=2..200')
    for n in range(2,13):
        gaps = brute_gaps(n)
        ap = lifted_apery(n)
        for power in range(4):
            assert gap_moment(ap,power) == sum(t**power for t in gaps)
    print('PASS gap moments p=0..3 against direct dynamic programming, n=2..12')
    assert all(frobenius(n+1) > frobenius(n) for n in range(2,1000))
    for n in range(42,1001):
        assert sum(D[j]*frobenius(n-j) for j in range(19)) == 0
    assert sum(D[j]*frobenius(41-j) for j in range(19)) == 2400
    print('PASS recurrence n=42..1000; nonzero boundary residual at n=41')
    for n in range(2,301):
        assert inverse_index(frobenius(n)) == n
        assert inverse_index(frobenius(n+1)-1) == n
    print('PASS exact inverse at both ends of each interval, n=2..300')
    if symbolic:
        symbolic_checks()
    out_dir.mkdir(parents=True,exist_ok=True)
    with (out_dir/'data.csv').open('w',newline='',encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow(['n','s_n','s_n_plus_1','s_n_plus_2','F_n','genus','symmetry_defect'])
        for n in range(2,1001):
            writer.writerow([n,pyr(n),pyr(n+1),pyr(n+2),frobenius(n),genus(n),2*genus(n)-frobenius(n)-1])
    print(f'ALL CHECKS PASSED ({time.perf_counter()-start:.2f} seconds)')
    print('Finite checks are not a Lean/Rocq formalization and do not establish novelty.')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--symbolic',action='store_true',help='also check polynomial identities with SymPy')
    parser.add_argument('--out-dir',type=Path,default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    run_checks(args.out_dir,args.symbolic)
