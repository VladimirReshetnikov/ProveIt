"""Finite Ramsey witnesses for small inputs, with a constructive one-rank reduction.

Vertex i is bit i. A table is indexed by all subset masks; only entries of
the specified arity affect the coloring. Bounds in the proof can be enormous.
The search here uses the supplied finite vertex set directly.
"""

from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
from typing import Callable


@lru_cache(maxsize=4096)
def submasks(mask: int, size: int) -> tuple[int, ...]:
    """The size-element submasks, in increasing numerical order."""
    if mask < 0 or size < 0:
        raise ValueError("mask and size must be nonnegative")
    if size > mask.bit_count():
        return ()
    bits = [1 << i for i in range(mask.bit_length()) if mask & (1 << i)]
    return tuple(sorted(sum(group) for group in combinations(bits, size)))


@dataclass(frozen=True)
class Coloring:
    n: int
    arity: int
    colors: int
    digits: tuple[int, ...]

    def __post_init__(self) -> None:
        if min(self.n, self.arity) < 0 or self.colors < 1:
            raise ValueError("need nonnegative dimensions and at least one color")
        if len(self.digits) != 1 << self.n:
            raise ValueError("need exactly one digit per subset mask")
        if any(not 0 <= digit < self.colors for digit in self.digits):
            raise ValueError("digit outside color range")

    @classmethod
    def tabulate(cls, n: int, arity: int, colors: int,
                 color: Callable[[int], int]) -> "Coloring":
        if min(n, arity) < 0 or colors < 1:
            raise ValueError("need nonnegative dimensions and at least one color")
        digits = [0] * (1 << n)
        for mask in submasks((1 << n) - 1, arity):
            digits[mask] = color(mask)
        return cls(n, arity, colors, tuple(digits))

    def encode(self) -> int:
        """Base max(2,colors), least-significant digit at mask 0."""
        base = max(2, self.colors)
        code = 0
        for digit in reversed(self.digits):
            code = base * code + digit
        return code

    @classmethod
    def decode(cls, n: int, arity: int, colors: int, code: int) -> "Coloring":
        if min(n, arity, code) < 0 or colors < 1:
            raise ValueError("invalid dimensions, color count, or code")
        digits = []
        for _ in range(1 << n):
            code, digit = divmod(code, max(2, colors))
            digits.append(digit)
        if code:
            raise ValueError("code has too many digits")
        return cls(n, arity, colors, tuple(digits))


@dataclass(frozen=True)
class Witness:
    mask: int
    color: int


def verify(table: Coloring, k: int, witness: Witness) -> bool:
    """Check membership, exact size, color range, and every induced edge."""
    mask = witness.mask
    return (0 <= mask < (1 << table.n)
            and mask.bit_count() == k
            and 0 <= witness.color < table.colors
            and all(table.digits[a] == witness.color
                    for a in submasks(mask, table.arity)))


def find_witness(table: Coloring, k: int) -> Witness | None:
    """Least mask of the requested size; use color zero for vacuous homogeneity."""
    if k < 0:
        raise ValueError("target size must be nonnegative")
    for mask in submasks((1 << table.n) - 1, k):
        edges = submasks(mask, table.arity)
        color = table.digits[edges[0]] if edges else 0
        if all(table.digits[a] == color for a in edges):
            return Witness(mask, color)
    return None


def bound_up_to(arity: int, target: int, colors: int, cap: int) -> int | None:
    """Return the sharpened uniform bound U when U <= cap, or None otherwise.

    Cap the binomial exponent during its computation and the power during
    multiplication. This also gives an effective comparison for high arity.
    """
    if min(arity, target, cap) < 0 or colors < 1:
        raise ValueError("invalid dimensions, color count, or cap")
    if arity == 0 or target <= arity or colors == 1:
        return target if target <= cap else None
    m = colors * (target - arity) + 1
    for d in range(1, arity):
        if m >= cap:
            return None
        # binom(m-1,d) is computed along its nondecreasing first half.
        n = m - 1
        exponent = 0 if d > n else 1
        for j in range(1, min(d, n - d) + 1):
            exponent = exponent * (n - j + 1) // j
            if exponent >= cap.bit_length():
                return None
        m += 1
        for _ in range(exponent):
            if m > cap // colors:
                return None
            m *= colors
    return m if m <= cap else None


def image_mask(mask: int, vertices: tuple[int, ...]) -> int:
    """Embed a mask on [len(vertices)] into the ambient vertex set."""
    if not 0 <= mask < 1 << len(vertices):
        raise ValueError("mask outside the embedded vertex set")
    return sum(1 << vertex for i, vertex in enumerate(vertices) if mask & (1 << i))


@dataclass(frozen=True)
class Reduction:
    vertices: tuple[int, ...]
    sentinel: int
    reduced: Coloring

    def lift(self, witness: Witness) -> Witness:
        """Embed a lower-rank witness and adjoin the sentinel, gaining one point."""
        mask = image_mask(witness.mask, self.vertices) | (1 << self.sentinel)
        return Witness(mask, witness.color)


def stabilize(table: Coloring, length: int) -> Reduction | None:
    """Find a stable prefix of prescribed length for a coloring of arity >=2.

    Before each pivot, process lower edges ending at the previous pivot. On
    small arbitrary inputs the reservoir can run out. The sharpened proof
    bound guarantees enough survivors. Ties favor the class encountered first.
    """
    if table.arity < 2 or length < 0:
        raise ValueError("need source arity at least two and nonnegative length")
    if length >= table.n:
        return None
    lower_arity = table.arity - 1
    survivors = list(range(table.n))
    selected = []
    prefix = 0
    for _ in range(length):
        if len(survivors) < 2:
            return None
        fresh_edges = ()
        if selected:
            previous_bit = 1 << selected[-1]
            tails = submasks(prefix ^ previous_bit, lower_arity - 1)
            fresh_edges = tuple(tail | previous_bit for tail in tails)
        classes: dict[tuple[int, ...], list[int]] = {}
        for y in survivors:
            profile = tuple(table.digits[edge | (1 << y)] for edge in fresh_edges)
            classes.setdefault(profile, []).append(y)
        largest = max(classes.values(), key=len)
        if len(largest) < 2:
            return None
        vertex = largest[0]
        survivors = largest[1:]
        selected.append(vertex)
        prefix |= 1 << vertex
    vertices = tuple(selected)
    sentinel = survivors[0]
    reduced = Coloring.tabulate(
        length, lower_arity, table.colors,
        lambda a: table.digits[image_mask(a, vertices) | (1 << sentinel)],
    )
    return Reduction(vertices, sentinel, reduced)


if __name__ == "__main__":
    cycle = {(1 << i) | (1 << ((i + 1) % 5)) for i in range(5)}
    for n in (5, 6):
        table = Coloring.tabulate(n, 2, 2, lambda edge: int(edge in cycle))
        witness = find_witness(table, 3)
        if witness is None:
            print(f"K{n}: no monochromatic triangle")
        else:
            vertices = [i for i in range(n) if witness.mask & (1 << i)]
            print(f"K{n}: monochromatic triangle {vertices} in color {witness.color}")
