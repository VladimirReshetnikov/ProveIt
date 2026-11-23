#!/usr/bin/env python3
"""The explicit bounded construction in the accompanying iPRA proof.

All data are integers. Every search and loop has a bound fixed before it
starts. Early exits merely omit absorbing iterations. This is executable
evidence for the algorithm, not a formal proof of its universal correctness.

The mathematical domain of inputs is the natural numbers. `prime_rep` is
total on that domain but promises a representation only for prime inputs.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable
import argparse
import json

Quad = tuple[int, int, int, int]
ZERO: Quad = (0, 0, 0, 0)
ONE: Quad = (1, 0, 0, 0)


def norm(x: Quad) -> int:
    return sum(a * a for a in x)


def conj(x: Quad) -> Quad:
    a, b, c, d = x
    return a, -b, -c, -d


def mul(x: Quad, y: Quad) -> Quad:
    """Hamilton product; the norm is Euler's four-square form."""
    a, b, c, d = x
    e, f, g, h = y
    return (
        a * e - b * f - c * g - d * h,
        a * f + b * e + c * h - d * g,
        a * g - b * h + c * e + d * f,
        a * h + b * g - c * f + d * e,
    )


def first_below(bound: int, pred: Callable[[int], bool]) -> int:
    """Return the first successful index < bound, or bound on failure.

The proof uses this as a schema for fixed primitive recursive predicates,
not as a universal evaluator of arbitrary primitive recursive program codes.
"""
    for i in range(bound):
        if pred(i):
            return i
    return bound


def least_divisor(q: int) -> int:
    """Least divisor >= 2, for q >= 2; return 1 for q < 2."""
    if q < 2:
        return 1
    offset = first_below(q - 1, lambda i: q % (i + 2) == 0)
    return offset + 2 if offset < q - 1 else q


def is_prime(p: int) -> bool:
    return p >= 2 and least_divisor(p) == p


def centered(z: int, m: int) -> int:
    """Signed representative in [-floor(m/2), floor(m/2)] for odd m."""
    if m <= 0:
        return z
    r = z % m
    return r if 2 * r <= m else r - m


def pair_by_parity(x: Quad) -> Quad:
    """Deterministic pairing. Correctly pairs equal parities when norm is even."""
    a, b, c, d = x
    if (a - b) % 2 == 0:
        return a, b, c, d
    if (a - c) % 2 == 0:
        return a, c, b, d
    return a, d, b, c


def halve(x: Quad) -> Quad:
    a, b, c, d = pair_by_parity(x)
    return (a + b) // 2, (a - b) // 2, (c + d) // 2, (c - d) // 2


@dataclass(frozen=True)
class State:
    m: int
    x: Quad


def seed(p: int) -> State:
    """Bounded seed search, lexicographic in (a,b); explicit failure default."""
    if p == 2:
        return State(1, (1, 1, 0, 0))
    if p < 3:
        return State(1, ZERO)
    width = (p - 1) // 2 + 1
    bound = width * width
    hit = first_below(bound, lambda i: ((i // width) ** 2 + (i % width) ** 2 + 1) % p == 0)
    if hit == bound:
        return State(1, ZERO)
    a, b = divmod(hit, width)
    x = (a, b, 1, 0)
    return State(norm(x) // p, x)


def step(s: State) -> State:
    """Total descent operation. Its correctness assumes norm(x)=m*p, 0<m<p."""
    m, x = s.m, s.x
    if m <= 1:
        return s
    if m % 2 == 0:
        return State(m // 2, halve(x))
    r = tuple(centered(a, m) for a in x)
    z = mul(x, conj(r))
    return State(norm(r) // m, tuple(a // m for a in z))


def prime_rep(p: int, *, literal_clock: bool = False) -> Quad:
    """At most p iterations; for prime p the output has norm p."""
    s = seed(p)
    for _ in range(p):
        if not literal_clock and s.m <= 1:
            break
        s = step(s)
    return s.x


def prime_trace(p: int) -> list[dict]:
    """Record the active part of the bounded prime construction."""
    s = seed(p)
    rows: list[dict] = [{"branch": "seed", "m": s.m, "x": s.x, "norm": norm(s.x)}]
    for _ in range(p):
        if s.m <= 1:
            break
        branch = "even-halving" if s.m % 2 == 0 else "odd-centered"
        row: dict = {"branch": branch, "old_m": s.m}
        if s.m % 2:
            r = tuple(centered(a, s.m) for a in s.x)
            row.update(residues=r, product=mul(s.x, conj(r)))
        s = step(s)
        row.update(m=s.m, x=s.x, norm=norm(s.x))
        rows.append(row)
    return rows


def four_squares(n: int, *, literal_clock: bool = False) -> Quad:
    """Natural four-square witnesses, with a loop bounded by the original n."""
    if n < 0:
        raise ValueError("The input must be a natural number.")
    if n == 0:
        return ZERO
    q, x = n, ONE
    for _ in range(n):
        if q == 1:
            if not literal_clock:
                break
            continue
        p = least_divisor(q)
        x = mul(x, prime_rep(p, literal_clock=literal_clock))
        q //= p
    return tuple(abs(a) for a in x)


def bounded_reference(n: int) -> Quad:
    """Independent bounded enumeration, used only for small validation cases."""
    from math import isqrt
    top = isqrt(n)
    pairs: dict[int, tuple[int, int]] = {}
    for a in range(top + 1):
        for b in range(top + 1):
            if a * a + b * b <= n:
                pairs.setdefault(a * a + b * b, (a, b))
    for s, (a, b) in pairs.items():
        if n - s in pairs:
            c, d = pairs[n - s]
            return a, b, c, d
    return ZERO


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--prime-trace", action="store_true")
    parser.add_argument("--literal-clock", action="store_true")
    args = parser.parse_args()
    if args.prime_trace:
        print(json.dumps(prime_trace(args.n), indent=2))
    else:
        x = four_squares(args.n, literal_clock=args.literal_clock)
        print(json.dumps({"n": args.n, "witness": x, "sum_of_squares": norm(x)}, indent=2))


if __name__ == "__main__":
    main()
