#!/usr/bin/env python3
"""Exact ternary pair-count geometry and quadratic Diophantine compilers.

Python >= 3.10; standard library only. Naturals include zero.  The canonical
c=2 compiler has 24 natural witnesses and 24 quadratic residuals.  Its
sum of squares is an explicit polynomial of total degree four.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Iterable, Mapping, Sequence
import argparse
import json
from pathlib import Path


def integer(value: int) -> int:
    if type(value) is not int:
        raise TypeError("expected an integer (booleans are not accepted)")
    return value


def natural(value: int) -> int:
    integer(value)
    if value < 0:
        raise ValueError("expected a nonnegative integer")
    return value


@dataclass(frozen=True)
class Poly:
    """An immutable sparse integer polynomial; each monomial is a name tuple."""
    terms: tuple[tuple[tuple[str, ...], int], ...]

    def __post_init__(self) -> None:
        # Own a canonical immutable copy, including when input came from lists.
        d: dict[tuple[str, ...], int] = {}
        for monomial, coefficient in self.terms:
            integer(coefficient)
            if any(type(name) is not str or not name for name in monomial):
                raise TypeError("variable names must be nonempty strings")
            m = tuple(sorted(monomial))
            d[m] = d.get(m, 0) + coefficient
        object.__setattr__(self, "terms", tuple(sorted((m, c) for m, c in d.items() if c)))

    @staticmethod
    def const(value: int) -> Poly:
        return Poly((((), integer(value)),))

    @staticmethod
    def var(name: str) -> Poly:
        return Poly((((name,), 1),))

    @staticmethod
    def coerce(value: Poly | int) -> Poly:
        return value if isinstance(value, Poly) else Poly.const(value)

    def __add__(self, other: Poly | int) -> Poly:
        return Poly(self.terms + self.coerce(other).terms)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly(tuple((m, -c) for m, c in self.terms))

    def __sub__(self, other: Poly | int) -> Poly:
        return self + -self.coerce(other)

    def __rsub__(self, other: Poly | int) -> Poly:
        return self.coerce(other) - self

    def __mul__(self, other: Poly | int) -> Poly:
        other = self.coerce(other)
        return Poly(tuple((m + n, c * d) for m, c in self.terms for n, d in other.terms))

    __rmul__ = __mul__

    @property
    def degree(self) -> int:
        return max((len(m) for m, _ in self.terms), default=0)

    def evaluate(self, env: Mapping[str, int]) -> int:
        total = 0
        for monomial, coefficient in self.terms:
            v = coefficient
            for name in monomial:
                v *= integer(env[name])
            total += v
        return total

    def serial(self) -> list[dict]:
        return [{"coefficient": c, "monomial": list(m)} for m, c in self.terms]


@dataclass(frozen=True)
class System:
    parameters: tuple[str, ...]
    witnesses: tuple[str, ...]
    residuals: tuple[Poly, ...]
    label: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "parameters", tuple(self.parameters))
        object.__setattr__(self, "witnesses", tuple(self.witnesses))
        object.__setattr__(self, "residuals", tuple(self.residuals))
        names = self.parameters + self.witnesses
        if len(set(names)) != len(names):
            raise ValueError("duplicate parameter or witness name")
        used = {x for p in self.residuals for m, _ in p.terms for x in m}
        if not used <= set(names):
            raise ValueError("undeclared variable")

    def residual_values(self, env: Mapping[str, int]) -> tuple[int, ...]:
        return tuple(p.evaluate(env) for p in self.residuals)

    def verify(self, env: Mapping[str, int]) -> bool:
        for name in self.parameters + self.witnesses:
            natural(env[name])
        return all(v == 0 for v in self.residual_values(env))

    def polynomial(self) -> Poly:
        return sum((p * p for p in self.residuals), Poly.const(0))

    def serial(self) -> dict:
        polynomial = self.polynomial()
        return {
            "label": self.label,
            "domain": "All listed parameters and witnesses are nonnegative integers.",
            "parameters": list(self.parameters), "witnesses": list(self.witnesses),
            "residual_count": len(self.residuals),
            "max_residual_degree": max(p.degree for p in self.residuals),
            "polynomial_degree": polynomial.degree,
            "polynomial_monomials": len(polynomial.terms),
            "residuals": [p.serial() for p in self.residuals],
            "sum_of_squares_polynomial": polynomial.serial(),
        }


def pair_profile(word: Sequence[str], alphabet: Sequence[str] = ("A", "B", "C")):
    """Return counts and K_ij for alphabet-ordered distinct letter pairs."""
    alphabet = tuple(alphabet)
    if len(set(alphabet)) != len(alphabet):
        raise ValueError("alphabet must have distinct letters")
    index = {s: i for i, s in enumerate(alphabet)}
    counts = [0] * len(alphabet)
    pairs = {(i, j): 0 for i in range(len(alphabet)) for j in range(i + 1, len(alphabet))}
    for letter in word:
        if letter not in index:
            raise ValueError("letter outside declared alphabet")
        j = index[letter]
        for i in range(j):
            pairs[i, j] += counts[i]
        counts[j] += 1
    return tuple(counts), tuple(pairs.values())


def binary_word(a: int, b: int, k: int) -> str:
    """Construct a word with a A's, b B's and exactly k AB pairs."""
    a, b, k = map(natural, (a, b, k))
    if k > a * b:
        raise ValueError("pair count outside binary range")
    if a == 0:
        return "B" * b
    q, s = divmod(k, a)
    if q == b:
        return "A" * a + "B" * b
    return "B" * (b - q - 1) + "A" * s + "B" + "A" * (a - s) + "B" * q


def gap_vectors(total: int, c: int, moment: int) -> Iterable[tuple[int, ...]]:
    """Enumerate x>=0 with sum x=total and sum (c-i)x_i=moment."""
    total, c, moment = map(natural, (total, c, moment))
    if moment > total * c:
        return
    def rec(n: int, weight: int, s: int, prefix: tuple[int, ...]):
        if weight == 0:
            if s == 0:
                yield prefix + (n,)
            return
        for x in range(min(n, s // weight) + 1):
            rest = s - weight * x
            if rest <= (weight - 1) * (n - x):
                yield from rec(n - x, weight - 1, rest, prefix + (x,))
    yield from rec(total, c, moment, ())


def gap_bounds(x: Sequence[int], y: Sequence[int]) -> tuple[int, int]:
    x, y = tuple(map(natural, x)), tuple(map(natural, y))
    if len(x) != len(y) or not x:
        raise ValueError("matching nonempty gap vectors required")
    prefix = lower = diagonal = 0
    for xi, yi in zip(x, y):
        lower += prefix * yi
        diagonal += xi * yi
        prefix += xi
    return lower, lower + diagonal


def general_bounds(a: int, b: int, c: int, p: int, q: int) -> tuple[int, int] | None:
    a, b, c, p, q = map(natural, (a, b, c, p, q))
    if p > a * c or q > b * c:
        return None
    lows, highs = [], []
    for x in gap_vectors(a, c, p):
        for y in gap_vectors(b, c, q):
            lo, hi = gap_bounds(x, y)
            lows.append(lo); highs.append(hi)
    return min(lows), max(highs)


def corner_bounds(a: int, b: int, p: int, q: int) -> tuple[int, int] | None:
    a, b, p, q = map(natural, (a, b, p, q))
    if p > 2 * a or q > 2 * b:
        return None
    xs, ys = (max(0, p - a), p // 2), (max(0, q - b), q // 2)
    lows, highs = [], []
    for x, y in product(xs, ys):
        lo = b*p - b*x - p*q + p*y + 2*q*x - 3*x*y
        hi = a*b - a*q + a*y + p*q - 2*p*y - q*x + 3*x*y
        lows.append(lo); highs.append(hi)
    return min(lows), max(highs)


def realize_gaps(a: int, b: int, c: int, p: int, q: int, k: int) -> str | None:
    """Small-instance constructor. Enumeration is not polynomial in bit size."""
    a, b, c, p, q, k = map(natural, (a, b, c, p, q, k))
    for x in gap_vectors(a, c, p):
        for y in gap_vectors(b, c, q):
            lo, hi = gap_bounds(x, y)
            if lo <= k <= hi:
                remaining = k - lo
                blocks = []
                for xi, yi in zip(x, y):
                    u = min(remaining, xi * yi)
                    blocks.append(binary_word(xi, yi, u))
                    remaining -= u
                assert remaining == 0
                return "C".join(blocks)
    return None


def normalization_path(word: str) -> Iterable[str]:
    """Construct the connected-fibre proof path (explicit, not compressed).

    Every yielded word has the original counts, K_AC and K_BC. Consecutive
    yielded words change K_AB by at most one. Both sides of a paired C swap
    are performed before yielding the next vertex.
    """
    if any(ch not in "ABC" for ch in word):
        raise ValueError("a ternary word is required")
    w = list(word)
    yield "".join(w)
    def positions(letter: str):
        gap = 0
        out = []
        for pos, ch in enumerate(w):
            if ch == "C": gap += 1
            elif ch == letter: out.append((gap, pos))
        return out
    for letter in "AB":
        while True:
            ps = positions(letter)
            if not ps or ps[-1][0] - ps[0][0] < 2:
                break
            lo, hi = ps[0][0], ps[-1][0]
            left = max(pos for gap, pos in ps if gap == lo)
            while w[left+1] != "C":
                w[left], w[left+1] = w[left+1], w[left]
                left += 1
                yield "".join(w)
            right = min(pos for gap, pos in positions(letter) if gap == hi)
            while w[right-1] != "C":
                w[right], w[right-1] = w[right-1], w[right]
                right -= 1
                yield "".join(w)
            assert left+1 < right-1
            w[left], w[left+1] = w[left+1], w[left]
            w[right], w[right-1] = w[right-1], w[right]
            yield "".join(w)
    # The gap counts now have their unique balanced values. Sort each gap.
    while True:
        swap = next((i for i in range(len(w)-1) if w[i:i+2] == ["B", "A"]), None)
        if swap is None:
            break
        w[swap], w[swap+1] = w[swap+1], w[swap]
        yield "".join(w)


def gap_system(c: int) -> System:
    c = natural(c)
    a, b, p, q, k = (Poly.var(n) for n in ("a", "b", "p", "q", "k"))
    xs = [Poly.var(f"x{i}") for i in range(c + 1)]
    ys = [Poly.var(f"y{i}") for i in range(c + 1)]
    u, v = Poly.var("u"), Poly.var("v")
    lower = sum((xs[i] * ys[j] for i in range(c + 1) for j in range(i + 1, c + 1)), Poly.const(0))
    diagonal = sum((xs[i] * ys[i] for i in range(c + 1)), Poly.const(0))
    residuals = (
        sum(xs, Poly.const(0)) - a, sum(ys, Poly.const(0)) - b,
        sum(((c-i)*xs[i] for i in range(c+1)), Poly.const(0)) - p,
        sum(((c-i)*ys[i] for i in range(c+1)), Poly.const(0)) - q,
        k - lower - u, diagonal - u - v,
    )
    names = tuple(f"x{i}" for i in range(c+1)) + tuple(f"y{i}" for i in range(c+1)) + ("u", "v")
    return System(("a", "b", "p", "q", "k"), names, residuals, f"ternary_gap_c{c}")


def canonical_c2(env_input: Mapping[str, int] | None = None) -> tuple[System, dict[str, int] | None]:
    """Build the same symbolic system with or without a supplied instance.

    With an input, also evaluate its triangular candidate assignment.  That
    assignment can have negative final slacks on rejected instances.  It is
    a natural-number witness exactly when the instance is accepted.
    """
    parameters = ("a", "b", "p", "q", "k")
    env = None if env_input is None else {n: natural(env_input[n]) for n in parameters}
    a, b, p, q, k = (Poly.var(n) for n in parameters)
    names: list[str] = []
    residuals: list[Poly] = []
    def new(name: str, value: int | None = None) -> Poly:
        if name in names or name in parameters:
            raise ValueError("duplicate variable")
        names.append(name)
        if env is not None:
            env[name] = integer(value)  # type: ignore[arg-type]
        return Poly.var(name)
    def val(poly: Poly) -> int | None:
        return None if env is None else poly.evaluate(env)
    def split(poly: Poly, prefix: str) -> tuple[Poly, Poly]:
        value = val(poly)
        positive = new(prefix + "_plus", None if value is None else max(value, 0))
        negative = new(prefix + "_minus", None if value is None else max(-value, 0))
        residuals.extend((positive - negative - poly, positive * negative))
        return positive, negative
    def floor_half(poly: Poly, prefix: str) -> Poly:
        value = val(poly)
        f = new(prefix + "_floor", None if value is None else value // 2)
        e = new(prefix + "_rem", None if value is None else value % 2)
        residuals.extend((poly - 2*f - e, e*(e-1)))
        return f
    def slack(poly: Poly, name: str):
        z = new(name, val(poly))
        residuals.append(poly - z)
    xp, _ = split(p-a, "xlower")
    yp, _ = split(q-b, "ylower")
    xf, yf = floor_half(p, "p"), floor_half(q, "q")
    slack(2*a-p, "p_bound")
    slack(2*b-q, "q_bound")
    lows, highs = [], []
    for x, y in product((xp, xf), (yp, yf)):
        lows.append(b*p-b*x-p*q+p*y+2*q*x-3*x*y)
        highs.append(a*b-a*q+a*y+p*q-2*p*y-q*x+3*x*y)
    low, high = lows[0], highs[0]
    for i in range(1, 4):
        plus, _ = split(low-lows[i], f"min{i}")
        low = low-plus
        _, minus = split(high-highs[i], f"max{i}")
        high = high+minus
    slack(k-low, "lower_gap")
    slack(high-k, "upper_gap")
    system = System(parameters, tuple(names), tuple(residuals), "canonical_ternary_c2")
    assert len(system.witnesses) == len(system.residuals) == 24
    assert all(f.degree <= 2 for f in system.residuals)
    return system, env


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    exp = sub.add_parser("export", help="export the complete canonical quartic as JSON")
    exp.add_argument("output", type=Path)
    decision = sub.add_parser("decide", help="decide c=2 pair-profile realizability")
    for name in ("a", "b", "p", "q", "k"):
        decision.add_argument(name, type=int)
    args = parser.parse_args()
    if args.command == "export":
        system, _ = canonical_c2()
        args.output.write_text(json.dumps(system.serial(), indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {args.output}")
    else:
        system, env = canonical_c2({n: getattr(args, n) for n in ("a", "b", "p", "q", "k")})
        assert env is not None
        accepted = all(v >= 0 for v in env.values()) and system.verify(env)
        print(json.dumps({"accepted": accepted, "bounds": corner_bounds(args.a, args.b, args.p, args.q),
                          "witness": env if accepted else None}, indent=2))

if __name__ == "__main__":
    main()
