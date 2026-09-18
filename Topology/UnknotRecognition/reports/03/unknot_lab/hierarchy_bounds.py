"""Arithmetic audit of the notes' hierarchy bound, NOT a geometric backend.

These functions check claimed integer invariants. They do not establish that
a manifold or surface has the claimed invariants, nor that the needed global
bounds hold for an unknot-recognition algorithm.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence


@dataclass(frozen=True)
class HierarchyBound:
    digit_bound: int
    depth_bound: int

    def __post_init__(self) -> None:
        if type(self.digit_bound) is not int or self.digit_bound < 0:
            raise ValueError("digit_bound must be a nonnegative integer")
        if type(self.depth_bound) is not int or self.depth_bound < 1:
            raise ValueError("depth_bound must be a positive integer")

    def pad(self, digits: Sequence[int]) -> tuple[int, ...]:
        if len(digits) > self.depth_bound:
            raise ValueError("Hierarchy exceeds depth bound")
        if any(type(d) is not int or not 0 <= d <= self.digit_bound for d in digits):
            raise ValueError("Hierarchy digit exceeds its bound")
        return tuple(digits) + (0,) * (self.depth_bound - len(digits))

    def potential(self, digits: Sequence[int]) -> int:
        value = 0
        for digit in self.pad(digits):
            value = value * (self.digit_bound + 1) + digit
        return value

    def verify_reset(self, before: Sequence[int], after: Sequence[int], pivot: int) -> bool:
        """Compare full phases: same earlier digits, a strictly lower pivot digit."""
        old, new = self.pad(before), self.pad(after)
        if type(pivot) is not int or not 0 <= pivot < self.depth_bound:
            raise ValueError("Invalid pivot index")
        return (old[:pivot] == new[:pivot] and new[pivot] < old[pivot]
                and self.potential(new) < self.potential(old))

    def phase_bound(self) -> int:
        return (self.digit_bound + 1) ** self.depth_bound

    def visit_bound(self) -> int:
        return self.depth_bound * self.phase_bound()

    def conditional_work_bound(self, per_visit: int, outer_phases: int) -> int:
        for value in (per_visit, outer_phases):
            if type(value) is not int or value < 1:
                raise ValueError("Work and outer-phase bounds must be positive integers")
        return per_visit * outer_phases * self.visit_bound()


def cheeger_inequality_only(boundary_genus: int, region_genus: int,
                           level_genus: int) -> bool:
    """Only 3*b <= min(r,h-r); does NOT test the Heegaard/Morse hypotheses."""
    if any(type(x) is not int or x < 0 for x in
           (boundary_genus, region_genus, level_genus)):
        raise ValueError("Genera must be nonnegative integers")
    if region_genus > level_genus:
        raise ValueError("Region genus exceeds containing-level genus")
    return 3 * boundary_genus <= min(region_genus, level_genus - region_genus)
