"""Exact bounded lexicographic accounting; NOT a geometric hierarchy algorithm.

Checking a proposed digit update does not prove that a topology procedure
can produce that update, or that its per-update bit cost is small.
"""
from __future__ import annotations
from dataclasses import dataclass


@dataclass(frozen=True)
class HierarchyBudget:
    max_digit: int
    max_length: int

    def __post_init__(self) -> None:
        if type(self.max_digit) is not int or self.max_digit < 0:
            raise ValueError('max_digit must be a nonnegative integer')
        if type(self.max_length) is not int or self.max_length < 0:
            raise ValueError('max_length must be a nonnegative integer')

    @property
    def base(self) -> int:
        return self.max_digit + 1

    def pad(self, digits: tuple[int, ...] | list[int]) -> tuple[int, ...]:
        if len(digits) > self.max_length:
            raise ValueError('Hierarchy exceeds the given length bound')
        if any(type(d) is not int or not 0 <= d <= self.max_digit for d in digits):
            raise ValueError('Digit exceeds the stated bound')
        return tuple(digits) + (0,) * (self.max_length - len(digits))

    def value(self, digits: tuple[int, ...] | list[int]) -> int:
        answer = 0
        for digit in self.pad(digits):
            answer = answer * self.base + digit
        return answer

    @property
    def max_value(self) -> int:
        return self.base ** self.max_length - 1

    def verify_replacement(self, before: tuple[int, ...] | list[int],
                           after: tuple[int, ...] | list[int], index: int) -> int:
        """Return the strictly positive potential drop; index is zero-based.

        The prefix must be unchanged; the named digit must decrease. Arbitrary
        suffix rebuilding is allowed within the stated bounds. Both lists
        describe completed comparable states, not intermediate extension steps.
        """
        a, b = self.pad(before), self.pad(after)
        if type(index) is not int or not 0 <= index < self.max_length:
            raise ValueError('Invalid update index')
        if a[:index] != b[:index] or not b[index] < a[index]:
            raise ValueError('Not a strict first-changed-digit decrease')
        difference = self.value(a) - self.value(b)
        if difference <= 0:
            raise AssertionError('Mixed-radix decrease failed')
        return difference

    def conditional_operation_bound(self, *, restarts: int = 1,
                                    work_per_step: int = 1) -> int:
        """Bound assuming the caller has separately proved all given budgets.

        At most base^L completed states, <= L+1 work units per state, with
        `restarts` phases. This function certifies arithmetic, not geometry.
        """
        if any(type(x) is not int or x < 1 for x in (restarts, work_per_step)):
            raise ValueError('restarts and work_per_step must be positive integers')
        return restarts * work_per_step * (self.max_length + 1) * (self.max_value + 1)
