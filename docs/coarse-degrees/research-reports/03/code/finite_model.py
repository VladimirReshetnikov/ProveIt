"""Finite models for the column-coding and product-forcing arguments.

These functions do NOT compute a Turing jump, decide arbitrary halting, or
construct the infinite counterexample. Finite decision trees are a restricted,
fully decidable subclass of oracle computations. Python 3.10+, standard library.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterator, Optional, Union

Bits = tuple[int, ...]


def _check_bits(bits: Bits) -> None:
    if any(bit not in (0, 1) for bit in bits):
        raise ValueError("Expected binary values")


def column_index(n: int) -> int:
    """The exponent of 2 dividing n+1."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    x = n + 1
    return (x & -x).bit_length() - 1


def column_point(k: int, t: int) -> int:
    if min(k, t) < 0:
        raise ValueError("k and t must be nonnegative")
    return (1 << k) * (2 * t + 1) - 1


def column_count(k: int, n: int) -> int:
    if min(k, n) < 0:
        raise ValueError("k and n must be nonnegative")
    return (n >> k) - (n >> (k + 1))


def tail_count(k: int, n: int) -> int:
    if min(k, n) < 0:
        raise ValueError("k and n must be nonnegative")
    return n >> k


@dataclass(frozen=True)
class Condition:
    """A stem and finitely many column values frozen AFTER that stem.

Old stem entries need not match newly frozen values. Requiring such a match
would invalidate the extension step in the mathematical construction.
"""
    stem: Bits = ()
    frozen: Bits = ()

    def __post_init__(self) -> None:
        _check_bits(self.stem)
        _check_bits(self.frozen)

    def fixed_bit(self, n: int) -> Optional[int]:
        if n < 0:
            raise ValueError("n must be nonnegative")
        if n < len(self.stem):
            return self.stem[n]
        k = column_index(n)
        return self.frozen[k] if k < len(self.frozen) else None

    def allows(self, extension: Bits) -> bool:
        _check_bits(extension)
        if len(extension) < len(self.stem):
            return False
        return all(self.fixed_bit(n) in (None, bit)
                   for n, bit in enumerate(extension))

    def extend(self, extension: Bits) -> Condition:
        if not self.allows(extension):
            raise ValueError("The new stem violates an existing restraint")
        return Condition(extension, self.frozen)

    def freeze_next(self, bit: int) -> Condition:
        if bit not in (0, 1):
            raise ValueError("Expected a bit")
        return Condition(self.stem, self.frozen + (bit,))

    def pad(self, length: int, free_bit: int = 0) -> Condition:
        if length < len(self.stem):
            raise ValueError("Cannot shorten a stem")
        if free_bit not in (0, 1):
            raise ValueError("Expected a bit")
        bits = list(self.stem)
        for n in range(len(bits), length):
            bit = self.fixed_bit(n)
            bits.append(free_bit if bit is None else bit)
        return self.extend(tuple(bits))

    def extensions(self, length: int) -> Iterator[Bits]:
        """Exhaustive enumeration, exponential in the number of free bits."""
        if length < len(self.stem):
            return
        free = [n for n in range(length) if self.fixed_bit(n) is None]
        for assignment in product((0, 1), repeat=len(free)):
            values = dict(zip(free, assignment))
            result = []
            for n in range(length):
                bit = values[n] if n in values else self.fixed_bit(n)
                if bit is None:
                    raise RuntimeError("Missing assignment to a free position")
                result.append(bit)
            yield tuple(result)


@dataclass(frozen=True)
class Return:
    """None denotes divergence in this finite model."""
    value: Optional[int]


@dataclass(frozen=True)
class Query:
    index: int
    zero: Tree
    one: Tree

    def __post_init__(self) -> None:
        if self.index < 0:
            raise ValueError("Negative oracle query")


Tree = Union[Return, Query]


def support(tree: Tree) -> set[int]:
    if isinstance(tree, Return):
        return set()
    return {tree.index} | support(tree.zero) | support(tree.one)


def evaluate(tree: Tree, bits: Bits) -> Optional[int]:
    while isinstance(tree, Query):
        if tree.index >= len(bits):
            raise ValueError("Oracle string is too short for this query")
        tree = tree.one if bits[tree.index] else tree.zero
    return tree.value


def realizations(condition: Condition, tree: Tree) -> dict[Optional[int], Bits]:
    """Possible outputs with one witnessing stem for each output."""
    length = max(len(condition.stem), 1 + max(support(tree), default=-1))
    answer: dict[Optional[int], Bits] = {}
    for bits in condition.extensions(length):
        answer.setdefault(evaluate(tree, bits), bits)
    return answer


def cross_witness(p: Condition, q: Condition, left: tuple[Tree, ...],
                  right: tuple[Tree, ...]) -> Optional[tuple[int, Bits, Bits]]:
    """Find disagreement for these finite tables, NOT general functionals."""
    if len(left) != len(right):
        raise ValueError("Input domains must match")
    for n, (lt, rt) in enumerate(zip(left, right)):
        lv, rv = realizations(p, lt), realizations(q, rt)
        for a, alpha in lv.items():
            for b, beta in rv.items():
                if a is not None and b is not None and a != b:
                    return n, alpha, beta
    return None


def sparse_encode(description: Callable[[int], int],
                  oracle: Callable[[int], int], n: int) -> int:
    if n < 0:
        raise ValueError("n must be nonnegative")
    if n > 0 and n & (n - 1) == 0:
        return oracle(n.bit_length() - 1)
    return description(n)
