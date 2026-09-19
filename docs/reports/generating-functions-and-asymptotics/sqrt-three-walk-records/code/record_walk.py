#!/usr/bin/env python3
"""Exact arithmetic for the even-trace deterministic walks in the report.

Python 3.10+; standard library only. No floating-point decisions are made.
For D=4, the walk is sum((-1)**floor(sqrt(3)*j), j=1..N).
For general even D>=4, the slope is (D+sqrt(D*D-4))/2.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from math import isqrt
from typing import Iterator


def natural(value: int, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an integer")
    if value < 0:
        raise ValueError(f"{name} must be nonnegative")
    return value


@dataclass(frozen=True)
class EvenTraceWalk:
    D: int = 4

    def __post_init__(self) -> None:
        natural(self.D, "D")
        if self.D < 4 or self.D % 2:
            raise ValueError("D must be even and at least 4")

    def B(self, n: int) -> int:
        """floor(gamma*n), gamma=(D+sqrt(D^2-4))/2."""
        natural(n, "n")
        a = self.D // 2
        return a*n + isqrt((a*a-1)*n*n)

    def small(self, n: int) -> int:
        """floor(beta*n), beta=1/gamma; includes the special case n=0."""
        natural(n, "n")
        return 0 if n == 0 else self.D*n - self.B(n) - 1

    def step(self, n: int) -> int:
        """The n-th increment; n is positive."""
        natural(n, "n")
        if n == 0:
            raise ValueError("steps are numbered from 1")
        return 1 - 2*(self.B(n) & 1)

    def value(self, n: int) -> int:
        """S_D(n) from the proved shrinking recurrence, O(log n) iterations."""
        natural(n, "n")
        answer = 0
        while n:
            k = self.small(n) + 1
            m = self.small(k)
            distance = self.B(k) - n
            odd = k & 1
            answer += 1 - self.D*odd - (1-2*odd)*distance
            if not 0 <= m < n:
                raise ArithmeticError("descent invariant failed")
            n = m
        return answer

    def lift(self, n: int) -> int:
        """The first-passage lift F_D(n)=B(B(n)+2)."""
        natural(n, "n")
        return self.D*self.B(n) - n + 2*self.D - 1

    def record(self, index: int) -> tuple[int, int]:
        """Return (record position, walk value), with record 0=(0,0).

        Uses the constant-coefficient scalar recurrence, not repeated floors.
        The loop has floor(index/D) iterations; bit-operation costs grow with
        the size of the exact output integer.
        """
        natural(index, "index")
        q, seed = divmod(index, self.D)
        value = q if seed == 0 else -((self.D-1)*q+seed)
        if q == 0:
            return seed, value
        prev, cur = seed, self.lift(seed)
        trace, forcing = self.D*self.D-2, 2*(self.D-1)
        for _ in range(1, q):
            prev, cur = cur, trace*cur-prev+forcing
        return cur, value

    def records(self) -> Iterator[tuple[int, int, int]]:
        """Yield (index, position, value), in strictly increasing position."""
        current = list(range(self.D))
        following = [self.lift(s) for s in current]
        q = 0
        while True:
            for seed, position in enumerate(current):
                value = q if seed == 0 else -((self.D-1)*q+seed)
                yield self.D*q+seed, position, value
            current, following = following, [
                (self.D*self.D-2)*y-x+2*(self.D-1)
                for x, y in zip(current, following)
            ]
            q += 1

    def first_positive(self, level: int) -> int:
        natural(level, "level")
        return self.record(self.D*level)[0]

    def first_negative(self, level: int) -> int:
        natural(level, "level")
        if level == 0:
            return 0
        q, residual = divmod(level-1, self.D-1)
        return self.record(self.D*q+residual+1)[0]

    def extrema(self, n: int) -> tuple[int, int]:
        """Exact (minimum, maximum) on the whole interval 0..n."""
        natural(n, "n")
        lo = hi = 0
        for _, position, value in self.records():
            if position > n:
                break
            lo, hi = min(lo, value), max(hi, value)
        return lo, hi


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("walk", "record", "extrema"))
    parser.add_argument("n", type=int)
    parser.add_argument("--D", type=int, default=4)
    args = parser.parse_args()
    walk = EvenTraceWalk(args.D)
    if args.operation == "walk":
        result = {"D": args.D, "N": args.n, "S": walk.value(args.n)}
    elif args.operation == "record":
        position, value = walk.record(args.n)
        result = {"D": args.D, "index": args.n, "position": position, "S": value}
    else:
        low, high = walk.extrema(args.n)
        result = {"D": args.D, "N": args.n, "minimum": low, "maximum": high}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
