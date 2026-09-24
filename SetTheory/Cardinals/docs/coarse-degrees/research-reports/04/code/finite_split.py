"""Exact, FINITE analogue of the cross-splitting lemma.

A TableFunctional gives every output, including divergence (None), for a
specified finite collection of inputs and a fixed finite oracle support.
Consequently exhaustive search here is complete for that finite model.
It is NOT a decision procedure for arbitrary oracle Turing machines.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterator

from density_coding import column

Bits = tuple[int, ...]


def bits_of(n: int, width: int) -> Bits:
    if type(n) is not int or type(width) is not int or width < 0 or not 0 <= n < (1 << width):
        raise ValueError("expected a natural number fitting the requested width")
    return tuple((n >> (width - 1 - j)) & 1 for j in range(width))


def bits_index(bits: Bits) -> int:
    value = 0
    for bit in bits:
        if bit not in (0, 1):
            raise ValueError("a binary tuple is required")
        value = (value << 1) | bit
    return value


@dataclass(frozen=True)
class Lock:
    """Stem sigma, and the finitely many locked column values A|k."""
    stem: Bits
    values: Bits

    def __post_init__(self) -> None:
        bits_index(self.stem)
        bits_index(self.values)

    def admits(self, extension: Bits) -> bool:
        if len(extension) < len(self.stem):
            return False
        if extension[:len(self.stem)] != self.stem:
            return False
        for n in range(len(self.stem), len(extension)):
            bit = extension[n]
            if bit not in (0, 1):
                return False
            k = column(n)
            if k < len(self.values) and bit != self.values[k]:
                return False
        return True

    def extensions(self, length: int) -> Iterator[Bits]:
        if type(length) is not int or length < len(self.stem):
            raise ValueError("requested length precedes the stem")
        base = list(self.stem)
        free = []
        for n in range(len(self.stem), length):
            k = column(n)
            if k < len(self.values):
                base.append(self.values[k])
            else:
                free.append(n)
                base.append(0)
        for assignment in product((0, 1), repeat=len(free)):
            extension = base.copy()
            for n, value in zip(free, assignment):
                extension[n] = value
            yield tuple(extension)

    def refine(self, extension: Bits) -> "Lock":
        if not self.admits(extension):
            raise ValueError("incompatible refinement")
        return Lock(extension, self.values)

    def add_column(self, value: int) -> "Lock":
        if value not in (0, 1):
            raise ValueError("new column value must be binary")
        return Lock(self.stem, self.values + (value,))


@dataclass(frozen=True)
class TableFunctional:
    """rows[n][i] is output on input n and width-bit oracle i.

    Each entry is a nonnegative integer, or None for divergence. Inputs
    outside these rows are deliberately not part of the finite model.
    """
    width: int
    rows: tuple[tuple[int | None, ...], ...]

    def __post_init__(self) -> None:
        if type(self.width) is not int or self.width < 0:
            raise ValueError("width must be a nonnegative integer")
        if any(len(r) != 1 << self.width for r in self.rows):
            raise ValueError("incorrect truth-table dimensions")
        for row in self.rows:
            if any(x is not None and (not isinstance(x, int) or x < 0)
                   for x in row):
                raise ValueError("entries must be natural numbers or None")

    def value(self, oracle: Bits, n: int) -> int | None:
        if type(n) is not int or not 0 <= n < len(self.rows):
            raise ValueError("input is outside the explicit finite model")
        if len(oracle) < self.width:
            raise ValueError("insufficient oracle support")
        return self.rows[n][bits_index(oracle[:self.width])]


@dataclass(frozen=True)
class SplitWitness:
    input: int
    left: Bits
    right: Bits
    left_output: int
    right_output: int


def find_split(
    left: Lock, right: Lock,
    phi: TableFunctional, psi: TableFunctional
) -> SplitWitness | None:
    """Exhaustive search on the EXPLICITLY FINITE domain of the tables.

    None is an exact no-split conclusion only for these supplied tables,
    not an assertion about the universal enumeration of Turing machines.
    """
    if len(phi.rows) != len(psi.rows):
        raise ValueError("functionals must have the same finite input domain")
    width = max(phi.width, psi.width, len(left.stem), len(right.stem))
    ls = tuple(left.extensions(width))
    rs = tuple(right.extensions(width))
    for n in range(len(phi.rows)):
        left_values = {}
        right_values = {}
        for sigma in ls:
            value = phi.value(sigma, n)
            if value is not None:
                left_values.setdefault(value, sigma)
        for tau in rs:
            value = psi.value(tau, n)
            if value is not None:
                right_values.setdefault(value, tau)
        for a, sigma in left_values.items():
            for b, tau in right_values.items():
                if a != b:
                    return SplitWitness(n, sigma, tau, a, b)
    return None


def finite_no_split_property(
    left: Lock, right: Lock,
    phi: TableFunctional, psi: TableFunctional
) -> bool:
    """Check the finite common-output consequence whenever no split exists."""
    if find_split(left, right, phi, psi) is not None:
        return True  # Implication has a false hypothesis.
    width = max(phi.width, psi.width, len(left.stem), len(right.stem))
    ls, rs = tuple(left.extensions(width)), tuple(right.extensions(width))
    for sigma in ls:
        for tau in rs:
            h = tuple(phi.value(sigma, n) for n in range(len(phi.rows)))
            g = tuple(psi.value(tau, n) for n in range(len(psi.rows)))
            if None not in h and h == g:
                for n, expected in enumerate(h):
                    possible = {phi.value(u, n) for u in ls} - {None}
                    if possible != {expected}:
                        return False
    return True
