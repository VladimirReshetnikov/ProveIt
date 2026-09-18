"""Arithmetic of a CONDITIONAL hierarchy bound; this is not a knot algorithm.

No function here constructs surfaces or proves any geometric complexity bound.
"""
from __future__ import annotations
from dataclasses import dataclass


@dataclass(frozen=True)
class HierarchyPotential:
    max_digit: int
    max_depth: int

    def __post_init__(self) -> None:
        if (type(self.max_digit) is not int or self.max_digit < 1
                or type(self.max_depth) is not int or self.max_depth < 1):
            raise ValueError("max_digit and max_depth must be positive integers")

    def value(self, digits: tuple[int, ...]) -> int:
        if len(digits) > self.max_depth:
            raise ValueError("hierarchy exceeds stipulated depth")
        if any(type(x) is not int or not 0 <= x <= self.max_digit for x in digits):
            raise ValueError("hierarchy digit outside stipulated bound")
        result = 0
        base = self.max_digit + 1
        for x in digits:
            result = result * base + x
        return result * base ** (self.max_depth - len(digits))

    def check_simplification(self, before: tuple[int, ...], after: tuple[int, ...],
                             first_changed: int) -> bool:
        old, new = self.value(before), self.value(after)
        if type(first_changed) is not int:
            return False
        j = first_changed
        if not 0 <= j < min(len(before), len(after)):
            return False
        return (before[:j] == after[:j] and after[j] < before[j] and new < old)

    @property
    def simplification_bound(self) -> int:
        return (self.max_digit + 1) ** self.max_depth - 1

    @property
    def loop_bound(self) -> int:
        """Bound if at most max_depth extension steps occur between decreases."""
        return self.max_depth * (self.max_digit + 1) ** self.max_depth
