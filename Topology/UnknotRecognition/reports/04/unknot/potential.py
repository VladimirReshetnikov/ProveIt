"""Arithmetic audit of bounded-depth hierarchy compression; NOT topology.

No function here constructs surfaces or proves the bounds g,L for a knot.
"""
from __future__ import annotations

from dataclasses import dataclass
from collections.abc import Iterable


@dataclass(frozen=True)
class HierarchyPotential:
    max_digit: int
    depth: int

    def __post_init__(self) -> None:
        if type(self.max_digit) is not int or self.max_digit < 0:
            raise ValueError("max_digit must be a nonnegative integer")
        if type(self.depth) is not int or self.depth < 0:
            raise ValueError("depth must be a nonnegative integer")

    @property
    def base(self) -> int:
        return self.max_digit + 1

    @property
    def phase_bound(self) -> int:
        return self.base ** self.depth

    @property
    def iteration_bound(self) -> int:
        return self.depth * self.phase_bound

    def digits(self, values: Iterable[int]) -> tuple[int, ...]:
        values = tuple(values)
        if len(values) > self.depth:
            raise ValueError("hierarchy exceeds the assumed depth bound")
        if any(type(value) is not int or not 0 <= value <= self.max_digit
               for value in values):
            raise ValueError("complexity digit outside the assumed bound")
        return values

    def value(self, values: Iterable[int]) -> int:
        digits = self.digits(values)
        value = 0
        for digit in digits:
            value = self.base * value + digit
        return value * self.base ** (self.depth - len(digits))

    def compress(self, values: Iterable[int], index: int, new_digit: int,
                 rebuilt_tail: Iterable[int] = ()) -> tuple[int, ...]:
        """Audit a proposed decrease, allowing an arbitrary newly rebuilt tail."""
        old = self.digits(values)
        if type(index) is not int or not 0 <= index < len(old):
            raise ValueError("compression index is outside the hierarchy")
        if type(new_digit) is not int or not 0 <= new_digit < old[index]:
            raise ValueError("the selected digit must strictly decrease")
        new = self.digits(old[:index] + (new_digit,) + tuple(rebuilt_tail))
        if self.value(new) >= self.value(old):
            raise ArithmeticError("potential did not decrease")
        return new
