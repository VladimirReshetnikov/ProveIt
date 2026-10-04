"""Cooperative budgets: exceeding a limit is UNKNOWN, never KNOTTED."""
from __future__ import annotations

from dataclasses import dataclass
from time import monotonic
import math


class BudgetExceeded(RuntimeError):
    pass


@dataclass(frozen=True)
class Limits:
    max_states: int | None = None
    max_generators: int | None = None
    seconds: float | None = None

    def __post_init__(self) -> None:
        for value in (self.max_states, self.max_generators):
            if value is not None and (type(value) is not int or value < 1):
                raise ValueError("Size budgets must be positive integers or None")
        if self.seconds is not None and (
                isinstance(self.seconds, bool) or not isinstance(self.seconds, (int, float))
                or not math.isfinite(self.seconds) or self.seconds <= 0):
            raise ValueError("Time budget must be a finite positive number or None")


class Budget:
    def __init__(self, limits: Limits | None = None) -> None:
        self.limits = limits or Limits()
        self.start = monotonic()
        self.deadline = (None if self.limits.seconds is None
                         else self.start + self.limits.seconds)

    def check(self) -> None:
        if self.deadline is not None and monotonic() >= self.deadline:
            raise BudgetExceeded("Cooperative time budget exhausted")

    def states(self, count: int) -> None:
        self.check()
        if self.limits.max_states is not None and count > self.limits.max_states:
            raise BudgetExceeded(f"{count} resolutions exceed max_states={self.limits.max_states}")

    def generators(self, count: int) -> None:
        self.check()
        if self.limits.max_generators is not None and count > self.limits.max_generators:
            raise BudgetExceeded(f"More than {self.limits.max_generators} chain generators")

    @property
    def elapsed(self) -> float:
        return monotonic() - self.start
