"""Checked numerical bookkeeping, NOT a geometric hierarchy constructor.

No number here establishes a bound for the unknot recognizer in solver.py.
"""
from __future__ import annotations
from dataclasses import dataclass


def pattern_complexity(euler_characteristic: int, pattern_intersections: int) -> int:
    if type(euler_characteristic) is not int or type(pattern_intersections) is not int:
        raise ValueError("Complexity inputs must be integers.")
    if pattern_intersections < 0:
        raise ValueError("Intersection counts cannot be negative.")
    return -4 * euler_characteristic + pattern_intersections


@dataclass(frozen=True)
class HierarchyBound:
    digit_bound: int
    depth_bound: int

    def __post_init__(self) -> None:
        if type(self.digit_bound) is not int or self.digit_bound < 0:
            raise ValueError("digit_bound must be a non-negative integer.")
        if type(self.depth_bound) is not int or self.depth_bound < 1:
            raise ValueError("depth_bound must be a positive integer.")

    def potential(self, digits: tuple[int, ...] | list[int]) -> int:
        if len(digits) > self.depth_bound:
            raise ValueError("Hierarchy exceeds the claimed depth bound.")
        if any(type(d) is not int or d < 0 or d > self.digit_bound for d in digits):
            raise ValueError("A complexity digit is outside the permitted range.")
        value = 0
        base = self.digit_bound + 1
        for i in range(self.depth_bound):
            value = value * base + (digits[i] if i < len(digits) else 0)
        return value

    def verify_rebuild(self, before: tuple[int, ...], after: tuple[int, ...], index: int) -> int:
        """Verify prefix preservation, decrease at index, and global rank decrease."""
        old, new = self.potential(before), self.potential(after)
        if type(index) is not int or not 0 <= index < min(len(before), len(after)):
            raise ValueError("Changed index is out of range.")
        if before[:index] != after[:index] or after[index] >= before[index]:
            raise ValueError("No strict decrease at the first changed surface.")
        if new >= old:
            raise ArithmeticError("A purported simplification did not lower the potential.")
        return old - new

    def iteration_bound(self) -> int:
        return self.depth_bound * (self.digit_bound + 1) ** self.depth_bound


def numerical_cheeger_inequality(boundary_genus: int, region_genus: int, level_genus: int) -> bool:
    """Only the inequality from the slides, NOT detection of a Cheeger region.

    The restricted Morse-function/Heegaard-surface conditions must be established
    geometrically before this test has the meaning asserted in the slides.
    """
    if any(type(x) is not int or x < 0 for x in (boundary_genus, region_genus, level_genus)):
        raise ValueError("Genera must be non-negative integers.")
    if region_genus > level_genus:
        raise ValueError("Region genus exceeds the containing level genus.")
    return 3 * boundary_genus <= min(region_genus, level_genus - region_genus)
