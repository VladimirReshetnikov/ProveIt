"""Exact arithmetic for the nonsplit Hasse classification. Python >= 3.10.

No floating-point arithmetic enters membership, reconstruction, or counting.
The asymptotic ratios printed by count.py are numerical illustrations only.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from math import gcd, isqrt


def keller(x, y, z):
    u = 1 + x*y
    h = u*u*z + y*y*(1+3*u)
    return u*h, y+3*x*h, x*(5-3*u-x*x*z)


def dyadic_condition(A: int, B: int, C: int) -> bool:
    c = C % 8
    if c == 0:
        return True
    if c == 4:
        return B % 2 == 0
    if c in (2, 6):
        return A % 2 == 0 and B % 2 == 0
    return ((A % 2 == 0 and B % 4 == 2)
            or (A % 2 == 1 and (B*C-2*A-1) % 8 == 0))


def odd_obstruction(A: int, B: int, C: int) -> int:
    g = gcd(3*B*C-4, 27*A*C*C-4)
    # 3*B*C-4 is never zero for integral B,C.
    while g % 2 == 0:
        g //= 2
    return g


def h_value(s: int, A: int, B: int, C: int) -> int:
    return s**3 - 2*s*s + B*C*s - 2*A*C*C


def reconstruct(s: int, A: int, B: int, C: int):
    """The point belonging to a simple integer root of H, for C != 0."""
    if C == 0 or h_value(s, A, B, C) != 0:
        raise ValueError('Require C != 0 and H(s) = 0.')
    D = 3*s*s - 4*s + B*C
    if D == 0:
        raise ValueError('Repeated roots do not give points in this chart.')
    point = (Fraction(2*C, D), Fraction(2*s-D, 2*C),
             Fraction(D*(10*D-12*s-D*D), 8*C*C))
    if keller(*point) != (A, B, C):
        raise ArithmeticError('Reconstruction failed exact substitution.')
    return point


def squarefree_divisors(n: int):
    """Yield (d, mu(d)) for squarefree positive divisors of n >= 1."""
    if n < 1:
        raise ValueError('n must be positive.')
    factors = []
    p = 2
    while p*p <= n:
        if n % p == 0:
            factors.append(p)
            while n % p == 0:
                n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        factors.append(n)
    pairs = [(1, 1)]
    for p in factors:
        pairs += [(d*p, -mu) for d, mu in pairs]
    return pairs


def count_primitive_b(r: int, lo: int, hi: int) -> int:
    if lo > hi:
        return 0
    total = 0
    for d, mu in squarefree_divisors(abs(3*r-1)):
        residue = 0 if d == 1 else pow(3, -1, d)
        total += mu*((hi-residue)//d - (lo-1-residue)//d)
    return total


def parameter_count(T: int) -> int:
    """Count marked integer roots in all locally soluble targets on C=2."""
    if T < 1:
        raise ValueError('T must be a positive integer.')
    bound = isqrt(2*T)+3
    total = 0
    for r in range(-bound, bound+1):
        lo, hi = -(T//2), T//2
        if r:
            center, radius = -r*r+r, T//abs(r)
            lo, hi = max(lo, center-radius), min(hi, center+radius)
        total += count_primitive_b(r, lo, hi)
    return total


def split_count(T: int) -> int:
    """Count locally soluble targets with three DISTINCT rational roots."""
    bound = isqrt(T+1)+2
    total = 0
    for r in range(-bound, 1):
        for s in range(r+1, (1-r)//2+1):
            t = 1-r-s
            if not s < t:
                continue
            b, A = r*s+r*t+s*t, r*s*t
            if abs(2*b) <= T and abs(A) <= T:
                if gcd(3*r-1, 3*b-1) == 1:
                    total += 1
    return total


def integral_targets(T: int):
    """The two exact integral-image curves, restricted to the target box."""
    bound = isqrt(T+1)+3  # deliberately loose, justified by the B-coordinate
    points = set()
    representations = []
    for r, eps in product(range(-bound, bound+1), (-1, 1)):
        A, B = -2*r**3+r*r+eps*r, -6*r*r+4*r+2*eps
        if abs(A) <= T and abs(B) <= T:
            point = (eps, r-eps, 5-eps*(3*r+2))
            assert keller(*point) == (A, B, 2)
            points.add((A, B))
            representations.append((r, eps))
    assert len(points) == len(representations), 'Unexpected collision of curves.'
    return points


def exact_counts(T: int):
    P, S, I = parameter_count(T), split_count(T), len(integral_targets(T))
    # The only repeated-root locally soluble target is (A,B)=(0,0).
    return {'T': T, 'marked_roots': P, 'split_hasse': S, 'integral': I,
            'locally_soluble_targets': P-2*S-1,
            'nonsplit_hasse': P-3*S-I-1, 'all_hasse': P-2*S-I-1}
