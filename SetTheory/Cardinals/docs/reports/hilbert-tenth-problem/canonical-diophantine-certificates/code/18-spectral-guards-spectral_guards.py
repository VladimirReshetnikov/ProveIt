"""Exact, non-expanding sign charts for integer polynomial-exponential sequences.

Python 3.10+, standard library only. All intervals are inclusive. Input
polynomials use ascending coefficients. No floating-point computations.
The proof of correctness is in the accompanying article, not in the tests.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import comb, factorial
from typing import Callable

def exact_integer(value: object) -> int:
    """Reject fractional JSON numbers and strings rather than silently coercing."""
    if type(value) is not int:
        raise ValueError("Expected an exact integer.")
    return value


@dataclass(frozen=True)
class Mode:
    base: int
    coefficients: tuple[int, ...]

@dataclass(frozen=True)
class Block:
    lo: int
    hi: int
    sign: int

@dataclass(frozen=True)
class Sequence:
    modes: tuple[Mode, ...]

    def __post_init__(self) -> None:
        if any(not isinstance(m, Mode) for m in self.modes):
            raise ValueError("Every mode must be a Mode instance.")
        bases = [exact_integer(m.base) for m in self.modes]
        for m in self.modes:
            for c in m.coefficients:
                exact_integer(c)
        if any(b < 1 for b in bases) or bases != sorted(set(bases)):
            raise ValueError("Bases must be distinct, positive integers, in order.")
        if any(not m.coefficients for m in self.modes):
            raise ValueError("Each declared mode needs at least one coefficient.")

    @property
    def dimension(self) -> int:
        return sum(len(m.coefficients) for m in self.modes)

    def value(self, t: int) -> int:
        exact_integer(t)
        if t < 0:
            raise ValueError("The time must be nonnegative.")
        total = 0
        for m in self.modes:
            p = 0
            for c in reversed(m.coefficients):
                p = p*t + c
            total += p * pow(m.base, t)
        return total

    def step(self) -> Sequence:
        """Apply E-b, where b is the first declared mode's base."""
        if not self.modes:
            return self
        b = self.modes[0].base
        out = []
        for i, m in enumerate(self.modes):
            c = m.coefficients
            size = len(c) - (i == 0)
            new = tuple(m.base * sum(comb(k, j)*c[k]
                                     for k in range(j, len(c))) - b*c[j]
                        for j in range(size))
            if new:
                out.append(Mode(m.base, new))
        return Sequence(tuple(out))

    def ladder(self) -> list[Sequence]:
        out = [self]
        while out[-1].dimension:
            out.append(out[-1].step())
        return out


def sign(n: int) -> int:
    return (n > 0) - (n < 0)


def append_block(out: list[Block], block: Block) -> None:
    if block.lo > block.hi:
        return
    if out and out[-1].hi + 1 != block.lo:
        raise ValueError("Blocks must be appended contiguously.")
    if out and out[-1].sign == block.sign:
        old = out[-1]
        out[-1] = Block(old.lo, block.hi, old.sign)
    else:
        out.append(block)


def lower_bound(lo: int, hi: int, predicate: Callable[[int], bool]) -> int:
    """First true point, or hi+1; predicate must be monotone false/true."""
    end = hi + 1
    while lo < end:
        mid = (lo + end)//2
        if predicate(mid):
            end = mid
        else:
            lo = mid + 1
    return lo


def monotone_pieces(seq: Sequence, lo: int, hi: int, direction: int,
                    evaluate: Callable[[int], int]) -> list[Block]:
    if lo > hi:
        return []
    if direction == 0:
        return [Block(lo, hi, sign(evaluate(lo)))]
    # The normalized sequence is monotone; its sign has the same ordering.
    oriented = lambda t: direction * sign(evaluate(t))
    first_nonnegative = lower_bound(lo, hi, lambda t: oriented(t) >= 0)
    first_positive = lower_bound(first_nonnegative, hi,
                                 lambda t: oriented(t) > 0)
    out: list[Block] = []
    for a, b, s in ((lo, first_nonnegative-1, -direction),
                    (first_nonnegative, first_positive-1, 0),
                    (first_positive, hi, direction)):
        if a <= b:
            out.append(Block(a, b, s))
    return out


def build_certificate(seq: Sequence, horizon: int) -> dict:
    """Construct canonical charts by binary searches, never scanning 0..T."""
    exact_integer(horizon)
    if horizon < 0 or seq.dimension < 1:
        raise ValueError("Require a nonnegative horizon and positive shape dimension.")
    ladder = seq.ladder()
    charts: list[list[Block]] = [[] for _ in ladder]
    charts[-1] = [Block(0, horizon, 0)]
    evaluations = 0
    max_value_bits = 0
    for r in range(len(ladder)-2, -1, -1):
        cache: dict[int, int] = {}
        def evaluate(t: int) -> int:
            nonlocal evaluations, max_value_bits
            if t not in cache:
                cache[t] = ladder[r].value(t)
                evaluations += 1
                max_value_bits = max(max_value_bits, abs(cache[t]).bit_length())
            return cache[t]
        out: list[Block] = []
        next_vertex = 0
        for lower in charts[r+1]:
            a = max(lower.lo, next_vertex)
            b = min(lower.hi+1, horizon)
            if a <= b:
                for piece in monotone_pieces(ladder[r], a, b,
                                             lower.sign, evaluate):
                    append_block(out, piece)
                next_vertex = b+1
        if next_vertex != horizon+1:
            raise AssertionError("The difference intervals failed to cover the domain.")
        if len(out) > max(1, 2*ladder[r].dimension-1):
            raise AssertionError("Chebyshev block bound violated.")
        charts[r] = out
    return {
        "horizon": horizon,
        "modes": [{"base": m.base, "coefficients": list(m.coefficients)}
                  for m in seq.modes],
        "charts": [[[b.lo, b.hi, b.sign] for b in row] for row in charts],
        "construction_statistics": {"evaluations": evaluations,
                                    "max_value_bits": max_value_bits},
    }


def decode_certificate(certificate: dict) -> tuple[Sequence, int, list[list[Block]]]:
    seq = Sequence(tuple(Mode(exact_integer(m["base"]), tuple(map(exact_integer, m["coefficients"])))
                         for m in certificate["modes"]))
    horizon = exact_integer(certificate["horizon"])
    charts = [[Block(*map(exact_integer, b)) for b in row] for row in certificate["charts"]]
    return seq, horizon, charts


def verify_certificate(certificate: dict) -> bool:
    """Endpoint-only verifier, independent of the chart-construction algorithm."""
    try:
        seq, T, charts = decode_certificate(certificate)
        ladder = seq.ladder()
        if T < 0 or seq.dimension < 1 or len(charts) != len(ladder):
            return False
        if charts[-1] != [Block(0, T, 0)]:
            return False
        for r, row in enumerate(charts):
            if not row or len(row) > max(1, 2*ladder[r].dimension-1):
                return False
            if row[0].lo != 0 or row[-1].hi != T:
                return False
            for i, b in enumerate(row):
                if not (0 <= b.lo <= b.hi <= T and b.sign in (-1, 0, 1)):
                    return False
                if i and (row[i-1].hi+1 != b.lo or row[i-1].sign == b.sign):
                    return False
        for r in range(len(ladder)-2, -1, -1):
            cache: dict[int, int] = {}
            for upper in charts[r]:
                for lower in charts[r+1]:
                    a = max(upper.lo, lower.lo)
                    b = min(upper.hi, lower.hi+1, T)
                    if a <= b:
                        for t in (a, b):
                            if t not in cache:
                                cache[t] = sign(ladder[r].value(t))
                            if cache[t] != upper.sign:
                                return False
        return True
    except (KeyError, TypeError, ValueError, IndexError, OverflowError):
        return False


def first_negative(certificate: dict) -> int | None:
    if not verify_certificate(certificate):
        raise ValueError("Not a valid certificate.")
    for lo, hi, s in certificate["charts"][0]:
        if s == -1:
            return lo
    return None


def tail_threshold(seq: Sequence) -> tuple[int, int]:
    """An elementary sufficient threshold, and the permanent tail sign.

    For n >= threshold, the sequence is nonzero and has tail_sign unless
    it is identically zero, in which case (0,0) is returned.
    """
    active = []
    for mode in seq.modes:
        c = list(mode.coefficients)
        while c and c[-1] == 0:
            c.pop()
        if c:
            active.append((mode.base, c))
    if not active:
        return 0, 0
    B, p = active[-1]
    m = len(p)-1
    A = sum(abs(c) for c in p[:-1])
    if len(active) == 1:
        return max(1, 2*A+1), sign(p[-1])
    b = active[-2][0]
    C = sum(abs(c) for _, q in active[:-1] for c in q)
    M = max(len(q)-1 for _, q in active[:-1])
    K = max(0, M-m)
    T = max(1, 2*(K+1), 2*A+1,
            (2**(K+2))*factorial(K+1)*(b**(K+1))*C+1)
    return T, sign(p[-1])


def brute_chart(seq: Sequence, T: int) -> list[Block]:
    out: list[Block] = []
    for t in range(T+1):
        append_block(out, Block(t, t, sign(seq.value(t))))
    return out
