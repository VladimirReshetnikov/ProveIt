"""Exact level-four, depth-two double-shuffle model.

No floating-point arithmetic is used here. A matrix rank refers only to the
stated linear product relations, never to independence of evaluated periods.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from functools import lru_cache
from math import comb
from typing import Optional
import sympy as sp

Coordinate = tuple[int, int, int, int]
COLORS = ((0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1))
X, Y = sp.symbols('X Y')
PI, LOG2 = sp.symbols('pi log2', real=True)

def valid_weight(w: int) -> None:
    if not isinstance(w, int) or isinstance(w, bool) or w < 2:
        raise ValueError('weight must be an integer >= 2')

def canonical(a: int, b: int, r: int, s: int) -> tuple[Optional[Coordinate], int]:
    r, s = r % 4, s % 4
    if r % 2 == s % 2 == 0:
        return None, 0
    opposite = (-r % 4, -s % 4)
    if (r, s) < opposite:
        return (a, b, r, s), 1
    return (a, b, *opposite), -1

def coordinates(w: int) -> list[Coordinate]:
    valid_weight(w)
    return [(a, w-a, r, s) for a in range(1, w) for r, s in COLORS
            if (a, r, s) != (1, 0, 1)]

@dataclass(frozen=True)
class Row:
    kind: str
    p: int
    q: int
    r: int
    s: int
    coefficients: tuple[int, ...]

@lru_cache(maxsize=None)
def rows(w: int) -> tuple[Row, ...]:
    """Keep all nonzero rows, including repeats: 92 rows in weight five."""
    cols = coordinates(w)
    result: list[Row] = []
    forbidden = (1, w-1, 0, 1)
    def add(d: dict, a: int, b: int, r: int, s: int, c: int) -> None:
        key, sign = canonical(a, b, r, s)
        if key is not None:
            d[key] += sign*c
    def emit(kind: str, p: int, q: int, r: int, s: int, d: dict) -> None:
        if d.get(forbidden, 0):
            raise ArithmeticError('divergent coordinate did not cancel')
        coeff = tuple(d.get(c, 0) for c in cols)
        if any(coeff):
            result.append(Row(kind, p, q, r, s, coeff))
    for p in range(1, w):
        q = w-p
        for r in range(4):
            for s in range(4):
                st, sh = defaultdict(int), defaultdict(int)
                add(st, p, q, r, s, 1)
                add(st, q, p, s, r, 1)
                for j in range(p):
                    add(sh, q+j, p-j, s, r-s, comb(q+j-1, j))
                for j in range(q):
                    add(sh, p+j, q-j, r, s-r, comb(p+j-1, j))
                if (p == 1 and r == 0) or (q == 1 and s == 0):
                    for key, value in sh.items():
                        st[key] -= value
                    emit('regularized_difference', p, q, r, s, st)
                else:
                    emit('stuffle', p, q, r, s, st)
                    emit('shuffle', p, q, r, s, sh)
    return tuple(result)

def matrix(w: int) -> sp.Matrix:
    return sp.Matrix([r.coefficients for r in rows(w)])

def mul(a: list[int], b: list[int]) -> list[int]:
    out = [0]*(len(a)+len(b)-1)
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            out[j+k] += x*y
    return out

def div_one_minus_t(a: list[int]) -> list[int]:
    """Exact division by (1-t), including a remainder check."""
    if len(a) < 2:
        raise ValueError('polynomial is too short')
    q = [a[0]]
    for c in a[1:-1]:
        q.append(c+q[-1])
    if a[-1] != -q[-1]:
        raise ArithmeticError('nonzero polynomial remainder')
    return q

def kernel_basis(w: int) -> sp.Matrix:
    """Integer nullspace basis in O(w^2) integer operations.

    Arrays represent P(1,t). Column families are B_j then C_j.
    The absent A coefficient is never included in the returned matrix.
    """
    cols = coordinates(w)
    if w % 2 == 0:
        return sp.zeros(len(cols), 0)
    n, m = w-2, (w-1)//2
    vectors: list[list[int]] = []
    zero = [0]*(n+1)
    # Build binomial rows by recurrences, charging O(w^2) integer updates.
    binom = []
    for degree in range(n+1):
        row = [1]
        for k in range(degree):
            row.append(row[-1]*(degree-k)//(k+1))
        binom.append(row+[0]*(n-degree))
    Bsmall = [-1, 2]
    E = mul([(1 if k%2 == 0 else -1)*binom[n-1][k] for k in range(n)], [1, 1])
    for j in range(m):
        B = Bsmall+[0]*(n+1-len(Bsmall))
        A = [-v for v in reversed(B)]
        color = {(0,1): A, (1,0): B, (1,3): E}
        vectors.append([color.get((r,s), zero)[b-1]
                        for a,b,r,s in cols])
        if j+1 < m:
            Bsmall = mul(Bsmall, [1, -4, 4])
            E = mul(div_one_minus_t(div_one_minus_t(E)), [1, 2, 1])
    for j in range(m):
        C = [0]*(n+1)
        C[n-j], C[j] = 1, -1
        F = [(1 if k%2 == 0 else -1)*(binom[n-j][k]-binom[j][k]) for k in range(n+1)]
        D = [-v for v in reversed(F)]
        color = {(1,1): C, (1,2): D, (2,1): F}
        vectors.append([color.get((r,s), zero)[b-1]
                        for a,b,r,s in cols])
    return sp.Matrix(len(cols), len(vectors), lambda i,j: vectors[j][i])

def predicted_ranks(w: int) -> tuple[int, int]:
    valid_weight(w)
    if w % 2:
        return 5*w-6, (9*w-11)//2
    return 6*w-7, 5*w-6

def row_membership(w: int, target: list) -> tuple[bool, Optional[list], Optional[sp.Expr]]:
    """Return membership, or an exact separating nullspace vector and pairing."""
    if len(target) != len(coordinates(w)):
        raise ValueError('target length does not match the coordinate order')
    t = sp.Matrix(1, len(target), [sp.Rational(v) for v in target])
    K = kernel_basis(w)
    pairings = t*K
    for j, value in enumerate(pairings):
        if value:
            return False, list(K[:,j]), value
    return True, None, None

@lru_cache(maxsize=None)
def zeta(n: int) -> sp.Expr:
    if n < 2:
        raise ValueError('zeta index must be >= 2')
    if n % 2:
        return sp.Symbol(f'zeta_{n}', real=True)
    k = n//2
    return (-1)**(k+1)*sp.bernoulli(n)*(2*PI)**n/(2*sp.factorial(n))

@lru_cache(maxsize=None)
def beta(n: int) -> sp.Expr:
    if n < 1:
        raise ValueError('beta index must be >= 1')
    if n % 2 == 0:
        return sp.Symbol(f'beta_{n}', real=True)
    k = (n-1)//2
    return (-1)**k*sp.euler(2*k)*PI**n/(4**(k+1)*sp.factorial(2*k))

@lru_cache(maxsize=None)
def single(n: int, r: int) -> sp.Expr:
    r %= 4
    if n == 1:
        return (sp.S.Zero, -LOG2/2+sp.I*PI/4, -LOG2, -LOG2/2-sp.I*PI/4)[r]
    if r == 0:
        return zeta(n)
    if r == 2:
        return (sp.Rational(2)**(1-n)-1)*zeta(n)
    re = sp.Rational(2)**(-n)*(sp.Rational(2)**(1-n)-1)*zeta(n)
    return re+(sp.I if r == 1 else -sp.I)*beta(n)

def imag(z: sp.Expr) -> sp.Expr:
    return sp.expand(sp.im(sp.expand(z)))

@lru_cache(maxsize=None)
def product_poly(w: int, r: int, s: int) -> sp.Expr:
    return sp.expand(sum(imag(single(p,r)*single(w-p,s))*X**(p-1)*Y**(w-p-1)
                         for p in range(1,w)))

def sub(f: sp.Expr, x: sp.Expr, y: sp.Expr) -> sp.Expr:
    return sp.expand(f.subs({X:x,Y:y}, simultaneous=True))

def affine_data(w: int) -> dict[str, sp.Expr]:
    n = w-2
    H = sum(X**j*Y**(n-j) for j in range(n+1))
    P01, P11, P12, P13 = [product_poly(w,r,s) for r,s in ((0,1),(1,1),(1,2),(1,3))]
    S01 = P01-beta(w)*H
    S12 = P12+beta(w)*H
    e = sub(P01,Y,X-Y)-sub(S01,X,X-Y)
    d = S12+sub(P12,X,Y-X)
    b = sub(P11,Y,X-Y)
    h = sub(P13,Y,Y-X)-sub(e,Y,Y-X)+sub(e,Y-X,Y)
    return {k:sp.expand(v) for k,v in locals().items()
            if k in ('P01','P11','P12','P13','S01','S12','e','d','b','h')}

def even_polynomials(w: int) -> dict[tuple[int,int], sp.Expr]:
    valid_weight(w)
    if w % 2:
        raise ValueError('the explicit unique solution requires even weight')
    t = affine_data(w)
    B = sp.expand((t['b']+t['h'])/2)
    C = sp.expand((sub(t['P13'],X,-Y)+sub(t['P11'],Y,X)
                  -sub(t['d'],X-Y,-Y)+sub(t['d'],X-Y,X))/2)
    A = sp.expand(t['S01']-sub(B,Y,X))
    E = sp.expand(sub(B,X-Y,X)+t['e'])
    F = sp.expand(sub(C,X,X-Y)-sub(t['P12'],Y,X-Y))
    D = sp.expand(-sub(C,Y,Y-X)+t['d'])
    return dict(zip(COLORS,(A,B,C,D,E,F)))

def even_values(w: int) -> list[sp.Expr]:
    pp = {c:sp.Poly(f,X,Y) for c,f in even_polynomials(w).items()}
    return [pp[r,s].coeff_monomial(X**(a-1)*Y**(b-1)) for a,b,r,s in coordinates(w)]

def rhs(row: Row) -> sp.Expr:
    z = imag(single(row.p+row.q, (row.r+row.s)%4))
    if row.kind == 'regularized_difference':
        return -z
    p = imag(single(row.p,row.r)*single(row.q,row.s))
    return p-z if row.kind == 'stuffle' else p
