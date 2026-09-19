#!/usr/bin/env python3
"""Exact arithmetic for polynomial divisibility of balanced factorial ratios.

No third-party dependencies.  This module constructs certificates; the separate
verify_certificates.py checks them without invoking the graph solver.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from math import factorial, gcd, isqrt, lcm, prod
from typing import Optional


@dataclass(frozen=True)
class Ratio:
    numerator: tuple[int, ...]
    denominator: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.numerator or not self.denominator:
            raise ValueError("Both parameter lists must be nonempty")
        if any(type(x) is not int or x <= 0 for x in self.numerator + self.denominator):
            raise ValueError("Parameters must be positive integers")
        if sum(self.numerator) != sum(self.denominator):
            raise ValueError("This implementation requires a balanced ratio")

    @property
    def height(self) -> int:
        return len(self.denominator) - len(self.numerator)

    @property
    def maximum(self) -> int:
        return max(self.numerator + self.denominator)

    @property
    def grid(self) -> int:
        return lcm(*(self.numerator + self.denominator))

    def delta(self, x: Fraction) -> int:
        return sum((a*x).__floor__() for a in self.numerator) - sum(
            (b*x).__floor__() for b in self.denominator)

    def jump(self, k: int) -> int:
        if k < 1:
            raise ValueError("k must be positive")
        return sum(a % k == 0 for a in self.numerator) - sum(
            b % k == 0 for b in self.denominator)

    def integral(self) -> bool:
        # Checking all breakpoints is enough, by right continuity.
        cuts = {Fraction(t, a) for a in self.numerator + self.denominator
                for t in range(a)}
        return all(self.delta(x) >= 0 for x in cuts)

    def value(self, n: int) -> Fraction:
        if n < 0:
            raise ValueError("n must be nonnegative")
        return Fraction(prod(factorial(a*n) for a in self.numerator),
                        prod(factorial(b*n) for b in self.denominator))

    def valuation(self, n: int, p: int) -> int:
        if n < 0 or p < 2:
            raise ValueError("Require n >= 0 and p >= 2 (prime)")
        q, total = p, 0
        while q <= self.maximum*n:
            total += sum(a*n//q for a in self.numerator)
            total -= sum(b*n//q for b in self.denominator)
            q *= p
        return total


@dataclass(frozen=True)
class Factor:
    slope: int
    offset: int
    multiplicity: int = 1

    def __post_init__(self) -> None:
        if self.slope < 1 or self.multiplicity < 1:
            raise ValueError("Slope and multiplicity must be positive")
        if gcd(self.slope, self.offset) != 1:
            raise ValueError("Normalize each factor to gcd(slope, offset)=1")

    @property
    def root(self) -> Fraction:
        return Fraction(-self.offset, self.slope)


A = Ratio((30, 1), (15, 10, 6))
B = Ratio((12, 1), (6, 4, 3))


def primes_upto(n: int) -> list[int]:
    if n < 2:
        return []
    sieve = bytearray(b'\x01')*(n+1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(n)+1):
        if sieve[p]:
            sieve[p*p:n+1:p] = b'\x00'*(((n-p*p)//p)+1)
    return [p for p in range(2, n+1) if sieve[p]]


def vp(n: int, p: int) -> int:
    """Exponent of the prime p in n; primality is a caller precondition."""
    if type(n) is not int or type(p) is not int or p < 2:
        raise ValueError("Require an integer n and a prime p >= 2")
    if n == 0:
        raise ValueError("The valuation of zero is not finite")
    n, e = abs(n), 0
    while n % p == 0:
        e += 1
        n //= p
    return e


def one_sided_capacity(ratio: Ratio, factor: Factor) -> int:
    if factor.offset == 0:
        return 0
    k = factor.slope
    vals = []
    for t in range(1, k+1):
        if gcd(t, k) == 1:
            val = ratio.delta(Fraction(t, k))
            if factor.offset > 0:
                val -= ratio.jump(k)
            vals.append(val)
    return min(vals)


def classify(ratio: Ratio, factors: tuple[Factor, ...]) -> bool:
    if not ratio.integral():
        raise ValueError("The ratio must satisfy Landau nonnegativity")
    if len({f.root for f in factors}) != len(factors):
        raise ValueError("Merge equal roots and add their multiplicities first")
    return all(f.offset != 0 and one_sided_capacity(ratio, f) >= f.multiplicity
               for f in factors)


def effective_bound(ratio: Ratio, factors: tuple[Factor, ...]) -> tuple[int, int]:
    """Return (cutoff B, multiplier lcm(1,...,B)^degree). Not generally optimal."""
    if not factors:
        return 1, 1
    if not classify(ratio, factors):
        raise ValueError("No fixed integer multiplier exists")
    resultants = [abs(f.slope*g.offset-g.slope*f.offset)
                  for i, f in enumerate(factors) for g in factors[i+1:]]
    cutoff = max([1, ratio.maximum*max(abs(f.offset) for f in factors)] + resultants)
    L = 1
    for j in range(1, cutoff+1):
        L = lcm(L, j)
    return cutoff, L**sum(f.multiplicity for f in factors)


def height_one_denominators(ratio: Ratio) -> tuple[list[int], list[int]]:
    if ratio.height != 1 or not ratio.integral():
        raise ValueError("Require an integral height-one ratio")
    return ([k for k in range(1, ratio.maximum+1) if ratio.jump(k) == -1],
            [k for k in range(1, ratio.maximum+1) if ratio.jump(k) == 1])


State = tuple[Optional[int], ...]


def certificate(ratio: Ratio, slopes: tuple[int, ...], p: int) -> dict:
    """Certificate for R(n)/prod(k*n+1), by a finite weighted digit graph."""
    if not classify(ratio, tuple(Factor(k, 1) for k in slopes)):
        raise ValueError("Only admissible, distinct factors are supported here")
    if p not in primes_upto(p):
        raise ValueError("p must be prime")
    L = ratio.grid
    delta = [ratio.delta(Fraction(j, L)) for j in range(L)]
    start = (0,) + (1,)*len(slopes)
    states, index, todo = [start], {start: 0}, deque([start])
    edges: list[tuple[int, int, int, int]] = []
    while todo:
        s = todo.popleft()
        u = index[s]
        for d in range(p):
            j = (int(s[0])+L*d)//p
            carries = tuple(None if t is None or (t+k*d) % p else (t+k*d)//p
                            for t, k in zip(s[1:], slopes))
            ns = (j,) + carries
            weight = delta[j] - sum(t is not None for t in carries)
            if ns not in index:
                index[ns] = len(states)
                states.append(ns)
                todo.append(ns)
            edges.append((u, index[ns], d, weight))
    terminal = index[(0,) + (None,)*len(slopes)]
    infinity = 10**9
    potential = [infinity]*len(states)
    potential[terminal] = 0
    for _ in range(len(states)):
        changed = False
        for u, v, d, w in edges:
            if potential[v] < infinity and w+potential[v] < potential[u]:
                potential[u] = w+potential[v]
                changed = True
        if not changed:
            break
    else:
        raise RuntimeError("Negative cycle; no valid bounded potential")
    if any(h == infinity for h in potential):
        raise RuntimeError("A state cannot reach the terminal")
    if any(potential[u] > w+potential[v] for u,v,d,w in edges):
        raise RuntimeError("Invalid potential")
    # A tight path gives an independently testable sharpness witness.
    adjacency: list[list[tuple[int, int]]] = [[] for _ in states]
    for u,v,d,w in edges:
        if potential[u] == w+potential[v]:
            adjacency[u].append((v,d))
    todo, parent = deque([0]), {0: None}
    while todo and terminal not in parent:
        u = todo.popleft()
        for v,d in adjacency[u]:
            if v not in parent:
                parent[v] = (u,d)
                todo.append(v)
    if terminal not in parent:
        raise RuntimeError("No tight witness path")
    digits, u = [], terminal
    while u != 0:
        u,d = parent[u]  # type: ignore[misc]
        digits.append(d)
    digits.reverse()
    witness = sum(d*p**e for e,d in enumerate(digits))
    actual = ratio.valuation(witness,p)-sum(vp(k*witness+1,p) for k in slopes)
    if actual != potential[0]:
        raise RuntimeError("Witness valuation mismatch")
    return {"numerator": list(ratio.numerator), "denominator": list(ratio.denominator),
            "slopes": list(slopes), "prime": p, "grid": L,
            "states": [list(s) for s in states], "potential": potential,
            "terminal": terminal, "minimum": potential[0], "witness": witness,
            "witness_digits_lsf": digits, "edge_count": len(edges)}
