"""Exact arithmetic and random access for 0 -> 1, 1 -> (10)^m.

Python 3.10+, standard library only. All decisions are exact; Decimal is
used only for human-readable numerical output. Positions and ranks are
1-based, whereas prefix lengths and positions stored in Extreme are 0-based.
"""
from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, localcontext
from typing import Optional


@dataclass(frozen=True)
class Quad:
    """a + b*q, where q^2 + m*q - m = 0 and 0 < q < 1."""
    m: int
    a: int = 0
    b: int = 0

    def __post_init__(self) -> None:
        if not all(isinstance(x, int) for x in (self.m, self.a, self.b)):
            raise TypeError("Quad requires integer parameters")
        if self.m < 1:
            raise ValueError("m must be positive")

    def _coerce(self, other: Quad | int) -> Quad:
        if isinstance(other, int):
            return Quad(self.m, other, 0)
        if not isinstance(other, Quad) or self.m != other.m:
            raise TypeError("incompatible quadratic fields")
        return other

    def __add__(self, other: Quad | int) -> Quad:
        v = self._coerce(other)
        return Quad(self.m, self.a + v.a, self.b + v.b)

    __radd__ = __add__

    def __neg__(self) -> Quad:
        return Quad(self.m, -self.a, -self.b)

    def __sub__(self, other: Quad | int) -> Quad:
        return self + (-self._coerce(other))

    def __rsub__(self, other: Quad | int) -> Quad:
        return self._coerce(other) - self

    def __mul__(self, other: Quad | int) -> Quad:
        v = self._coerce(other)
        bd = self.b * v.b
        return Quad(self.m, self.a * v.a + self.m * bd,
                    self.a * v.b + self.b * v.a - self.m * bd)

    __rmul__ = __mul__

    def sign(self) -> int:
        """Sign by integer squares, not a floating-point approximation."""
        a = 2 * self.a - self.m * self.b
        b = self.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        difference = a * a - (self.m * self.m + 4 * self.m) * b * b
        return ((difference > 0) - (difference < 0)) * ((a > 0) - (a < 0))

    def __lt__(self, other: Quad | int) -> bool:
        return (self - other).sign() < 0

    def decimal(self, precision: int = 60) -> Decimal:
        # Extra guard digits are needed when a and b nearly cancel.
        guard = max(len(str(abs(self.a))), len(str(abs(self.b)))) + 15
        with localcontext() as ctx:
            ctx.prec = precision + guard
            q = (Decimal(self.m * self.m + 4 * self.m).sqrt() - self.m) / 2
            result = Decimal(self.a) + self.b * q
            ctx.prec = precision
            return +result

    def as_dict(self) -> dict:
        return {"a": self.a, "b": self.b, "m": self.m}

    def __str__(self) -> str:
        return f"{self.a}{self.b:+d}*q"


@dataclass(frozen=True)
class Extreme:
    value: Quad
    position: int  # Number of preceding letters, not a 1-based position.


@dataclass(frozen=True)
class Summary:
    m: int
    zeros: int
    ones: int
    minimum: tuple[Optional[Extreme], Optional[Extreme]]
    maximum: tuple[Optional[Extreme], Optional[Extreme]]

    @property
    def length(self) -> int:
        return self.zeros + self.ones

    @property
    def weight(self) -> Quad:
        return Quad(self.m, self.zeros, -self.ones)

    def count(self, symbol: int) -> int:
        return self.ones if symbol == 1 else self.zeros


def empty_summary(m: int) -> Summary:
    return Summary(m, 0, 0, (None, None), (None, None))


def letter_summary(m: int, symbol: int) -> Summary:
    if symbol not in (0, 1):
        raise ValueError("symbol must be 0 or 1")
    e = Extreme(Quad(m), 0)
    extrema = (e, None) if symbol == 0 else (None, e)
    return Summary(m, int(symbol == 0), int(symbol == 1), extrema, extrema)


def concatenate(left: Summary, right: Summary) -> Summary:
    """Associative exact summary of a concatenation."""
    if left.m != right.m:
        raise ValueError("m must agree")
    minima, maxima = [], []
    for symbol in (0, 1):
        lists = []
        for operation in ("minimum", "maximum"):
            candidates = []
            a = getattr(left, operation)[symbol]
            b = getattr(right, operation)[symbol]
            if a is not None:
                candidates.append(a)
            if b is not None:
                candidates.append(Extreme(left.weight + b.value,
                                          left.length + b.position))
            if not candidates:
                lists.append(None)
            else:
                choose = min if operation == "minimum" else max
                lists.append(choose(candidates, key=lambda e: e.value))
        minima.append(lists[0])
        maxima.append(lists[1])
    return Summary(left.m, left.zeros + right.zeros, left.ones + right.ones,
                   tuple(minima), tuple(maxima))


class Substitution:
    """Finite blocks W[-1]=0, W[0]=1, W[k]=(W[k-1] W[k-2])^m."""

    def __init__(self, m: int = 3) -> None:
        if not isinstance(m, int) or m < 1:
            raise ValueError("m must be a positive integer")
        self.m = m
        self.blocks = {-1: letter_summary(m, 0), 0: letter_summary(m, 1)}
        self._highest = 0

    def block(self, k: int) -> Summary:
        if not isinstance(k, int) or k < -1:
            raise ValueError("block index must be at least -1")
        if k in self.blocks:
            return self.blocks[k]
        for j in range(self._highest + 1, k + 1):
            pair = concatenate(self.blocks[j - 1], self.blocks[j - 2])
            total = empty_summary(self.m)
            for _ in range(self.m):
                total = concatenate(total, pair)
            self.blocks[j] = total
        self._highest = k
        return self.blocks[k]

    def prefix_counts(self, length: int) -> tuple[int, int]:
        """Return (zeros, ones) in the first length letters in O(log length) steps."""
        if not isinstance(length, int) or length < 0:
            raise ValueError("length must be a nonnegative integer")
        k = 0
        while self.block(k).length < length:
            k += 1
        z = o = 0
        remaining = length
        while remaining:
            current = self.block(k)
            if remaining == current.length:
                return z + current.zeros, o + current.ones
            if k < 1:
                raise AssertionError("invalid residual length")
            a, b = self.block(k - 1), self.block(k - 2)
            pairs, remaining = divmod(remaining, a.length + b.length)
            z += pairs * (a.zeros + b.zeros)
            o += pairs * (a.ones + b.ones)
            if remaining > a.length:
                z += a.zeros
                o += a.ones
                remaining -= a.length
                k -= 2
            else:
                k -= 1
        return z, o

    def select(self, symbol: int, rank: int) -> int:
        """Return the 1-based position of the rank-th specified letter."""
        if symbol not in (0, 1) or not isinstance(rank, int) or rank < 1:
            raise ValueError("symbol must be 0 or 1 and rank must be positive")
        k = 0
        while self.block(k).count(symbol) < rank:
            k += 1
        position = 0
        while k >= 1:
            a, b = self.block(k - 1), self.block(k - 2)
            pair_count = a.count(symbol) + b.count(symbol)
            pairs = (rank - 1) // pair_count
            rank -= pairs * pair_count
            position += pairs * (a.length + b.length)
            if rank > a.count(symbol):
                rank -= a.count(symbol)
                position += a.length
                k -= 2
            else:
                k -= 1
        if self.block(k).count(symbol) != 1 or rank != 1:
            raise AssertionError("invalid select terminal state")
        return position + 1

    def first_at_least(self, symbol: int, threshold: int = 2,
                       max_level: int = 128) -> Optional[dict]:
        """Find the first position error >= threshold, using exact block pruning.

        None means no such position occurs in W[max_level]; it is not an
        assertion of nonexistence in the infinite word.
        """
        if symbol not in (0, 1) or not isinstance(threshold, int):
            raise ValueError("symbol must be 0 or 1 and threshold an integer")
        if max_level < 0:
            raise ValueError("max_level must be nonnegative")
        boundary = (Quad(self.m, -threshold, 1) if symbol == 1
                    else Quad(self.m, -1, threshold))

        def possible(k: int, z: int, o: int) -> bool:
            summary = self.block(k)
            extreme = (summary.minimum[symbol] if symbol == 1
                       else summary.maximum[symbol])
            if extreme is None:
                return False
            sign = (Quad(self.m, z, -o) + extreme.value - boundary).sign()
            return sign <= 0 if symbol == 1 else sign >= 0

        root = next((k for k in range(max_level + 1) if possible(k, 0, 0)), None)
        if root is None:
            return None
        k = root
        z = o = 0
        trace = []
        while k >= 1:
            skipped = []
            for child_index, child in enumerate([k - 1, k - 2] * self.m):
                if possible(child, z, o):
                    trace.append({"parent": k, "chosen_child": child_index,
                                  "child_level": child, "prefix_zeros": z,
                                  "prefix_ones": o, "skipped_levels": skipped})
                    k = child
                    break
                skipped.append(child)
                summary = self.block(child)
                z += summary.zeros
                o += summary.ones
            else:
                raise AssertionError("a feasible block had no feasible child")
        return {"m": self.m, "symbol": symbol, "threshold": threshold,
                "root_level": root, "position": z + o + 1,
                "rank": (o if symbol == 1 else z) + 1,
                "prefix_zeros": z, "prefix_ones": o, "trace": trace}


def direct_prefix(m: int, length: int) -> str:
    """Independent literal substitution, intended only for finite tests."""
    if m < 1 or length < 0:
        raise ValueError("invalid m or length")
    word = "1"
    images = {"0": "1", "1": "10" * m}
    while len(word) < length:
        word = "".join(images[c] for c in word)[:length]
    return word[:length]


def extremal_family(m: int, count: int) -> list[dict]:
    """Construct the family with E_1(n_j)=C*(1-q^(2*j+2))."""
    if m < 1 or count < 0:
        raise ValueError("invalid m or count")
    z = o = 0  # Counts of P_j, not sigma(P_j).
    rows = []
    for j in range(count):
        rank = z + m * o + 1
        position = z + 2 * m * o + 1
        error = Quad(m, rank - position, rank)
        rows.append({"j": j, "rank": rank, "position": position,
                     "error": error.as_dict(), "error_decimal": str(error.decimal())})
        z, o = (m * z + m * m * o + m,
                m * z + (m * m + m) * o + m)
    return rows
