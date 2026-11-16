#!/usr/bin/env python3
"""Exact reference algorithms for Scoped Certificate Realization (SCR).

This file is deliberately small and uses only the Python standard library.
It is evidence about the finite encodings described in the report.  It is not
an iPRA proof and does not replace the object-theory derivations proposed in
``lean/FORMALIZATION_PLAN.md``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Callable, Iterable, Sequence, TypeVar

T = TypeVar("T")


def pack_digits(digits: Sequence[int], base: int) -> int:
    """Pack little-endian digits into one natural number."""
    if base < 2:
        raise ValueError("base must be at least 2")
    code = 0
    place = 1
    for d in digits:
        if not 0 <= d < base:
            raise ValueError(f"digit {d} is outside [0,{base})")
        code += d * place
        place *= base
    return code


def digit(code: int, index: int, base: int) -> int:
    """Return one little-endian digit, with implicit trailing zeroes."""
    if code < 0 or index < 0 or base < 2:
        raise ValueError("natural code/index and base >= 2 required")
    return (code // (base**index)) % base


def unpack_digits(code: int, length: int, base: int) -> list[int]:
    return [digit(code, i, base) for i in range(length)]


def least_accepted(bound: int, accepts: Callable[[int], bool]) -> int:
    """The bounded-search convention used by SCR: return bound if none works."""
    if bound < 0:
        raise ValueError("bound must be natural")
    for candidate in range(bound):
        if accepts(candidate):
            return candidate
    return bound


@dataclass(frozen=True)
class PathCertificate:
    base: int
    horizon: int
    code: int
    states: tuple[int, ...]


def verify_state_path(
    code: int,
    *,
    base: int,
    horizon: int,
    start: int,
    edge: Callable[[int, int], bool],
    goal: Callable[[int], bool],
) -> tuple[bool, tuple[int, ...]]:
    """Verify a whole finite path encoded as its post-initial states.

    This is the finite-path discipline used instead of locally greedy choice.
    The verifier is a bounded fold: every state is decoded first, then all
    adjacent transitions and the final goal are checked.
    """
    states = (start, *unpack_digits(code, horizon, base))
    in_range = all(0 <= x < base for x in states)
    transitions = all(edge(states[i], states[i + 1]) for i in range(horizon))
    return in_range and transitions and goal(states[-1]), tuple(states)


def least_path_certificate(
    *,
    base: int,
    horizon: int,
    start: int,
    edge: Callable[[int, int], bool],
    goal: Callable[[int], bool],
) -> PathCertificate | None:
    """Select the least accepted whole-path code under the explicit base bound."""
    cutoff = base**horizon
    code = least_accepted(
        cutoff,
        lambda c: verify_state_path(
            c, base=base, horizon=horizon, start=start, edge=edge, goal=goal
        )[0],
    )
    if code == cutoff:
        return None
    ok, states = verify_state_path(
        code, base=base, horizon=horizon, start=start, edge=edge, goal=goal
    )
    assert ok
    return PathCertificate(base, horizon, code, states)


def cubic(y: Fraction) -> Fraction:
    return y * y * y + y


@dataclass(frozen=True)
class CubicBisectionCertificate:
    x: Fraction
    initial_lo: Fraction
    initial_hi: Fraction
    steps: int
    branch_code: int
    branches: tuple[int, ...]
    final_lo: Fraction
    final_hi: Fraction


def cubic_bisection_certificate(
    x: Fraction, lo: Fraction, hi: Fraction, steps: int
) -> CubicBisectionCertificate:
    """Produce an exact branch trace for y^3+y=x.

    Branch digit 1 keeps the right half (mid becomes the new lower endpoint);
    digit 0 keeps the left half (mid becomes the new upper endpoint).
    """
    if steps < 0 or lo > hi or not (cubic(lo) <= x <= cubic(hi)):
        raise ValueError("invalid initial bracket")
    a, b = lo, hi
    branches: list[int] = []
    for _ in range(steps):
        mid = (a + b) / 2
        if cubic(mid) <= x:
            branches.append(1)
            a = mid
        else:
            branches.append(0)
            b = mid
    return CubicBisectionCertificate(
        x=x,
        initial_lo=lo,
        initial_hi=hi,
        steps=steps,
        branch_code=pack_digits(branches, 2),
        branches=tuple(branches),
        final_lo=a,
        final_hi=b,
    )


def verify_cubic_bisection_certificate(c: CubicBisectionCertificate) -> bool:
    if c.steps < 0 or len(c.branches) != c.steps:
        return False
    if c.branch_code != pack_digits(c.branches, 2):
        return False
    if not (c.initial_lo <= c.initial_hi):
        return False
    if not (cubic(c.initial_lo) <= c.x <= cubic(c.initial_hi)):
        return False
    a, b = c.initial_lo, c.initial_hi
    for i in range(c.steps):
        branch = digit(c.branch_code, i, 2)
        if branch != c.branches[i]:
            return False
        mid = (a + b) / 2
        if branch == 1:
            if not cubic(mid) <= c.x:
                return False
            a = mid
        else:
            if not c.x < cubic(mid):
                return False
            b = mid
        if not (cubic(a) <= c.x <= cubic(b)):
            return False
    return (
        a == c.final_lo
        and b == c.final_hi
        and b - a == (c.initial_hi - c.initial_lo) / (2**c.steps)
    )


def fraction_text(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def symmetric_root_observation(roots: Sequence[Fraction]) -> tuple[Fraction, Fraction, Fraction]:
    """A branch-independent observation: sum, product, and sum of squares."""
    total = sum(roots, Fraction(0))
    prod_value = Fraction(1)
    sq = Fraction(0)
    for r in roots:
        prod_value *= r
        sq += r * r
    return total, prod_value, sq


def stable_observation(
    certificates: Iterable[T],
    *,
    valid: Callable[[T], bool],
    observe: Callable[[T], object],
) -> object:
    """Check exact observer independence across every supplied valid certificate."""
    values = [observe(c) for c in certificates if valid(c)]
    if not values:
        raise ValueError("no valid certificate")
    first = values[0]
    if any(v != first for v in values[1:]):
        raise ValueError("observer is not certificate-independent")
    return first


def curve_rhs(x: int) -> int:
    return x**3 - x + 1


def bounded_curve_points(height: int) -> tuple[tuple[int, int], ...]:
    """All integer points on y^2=x^3-x+1 in the square |x|,|y| <= height."""
    if height < 0:
        raise ValueError("height must be natural")
    points = [
        (x, y)
        for x in range(-height, height + 1)
        for y in range(-height, height + 1)
        if y * y == curve_rhs(x)
    ]
    return tuple(points)


def verify_bounded_curve_list(height: int, points: Sequence[tuple[int, int]]) -> bool:
    """Verify soundness, no duplicates, and completeness *inside* the supplied box."""
    normalized = tuple(sorted(set(points)))
    return (
        len(normalized) == len(points)
        and all(abs(x) <= height and abs(y) <= height for x, y in normalized)
        and all(y * y == curve_rhs(x) for x, y in normalized)
        and normalized == bounded_curve_points(height)
    )


def all_permutations(values: Sequence[T]) -> tuple[tuple[T, ...], ...]:
    """Small deterministic permutation generator, kept dependency-free."""
    if not values:
        return ((),)
    out: list[tuple[T, ...]] = []
    for i, x in enumerate(values):
        rest = values[:i] + values[i + 1 :]
        out.extend((x, *p) for p in all_permutations(rest))
    # Remove duplicates while preserving order.
    return tuple(dict.fromkeys(out))


def demo_payload() -> dict[str, object]:
    cubic_cert = cubic_bisection_certificate(
        Fraction(2), Fraction(0), Fraction(2), 8
    )
    graph_edges = {(0, 1), (0, 2), (1, 1), (1, 3), (2, 2), (2, 3), (3, 4)}
    path = least_path_certificate(
        base=5,
        horizon=3,
        start=0,
        edge=lambda a, b: (a, b) in graph_edges,
        goal=lambda s: s == 4,
    )
    roots = (Fraction(-2), Fraction(1), Fraction(3))
    certs = all_permutations(roots)
    observer = stable_observation(
        certs,
        valid=lambda c: sorted(c) == sorted(roots),
        observe=symmetric_root_observation,
    )
    points = bounded_curve_points(12)
    assert path is not None
    return {
        "cubic_bisection": {
            "x": fraction_text(cubic_cert.x),
            "initial": [fraction_text(cubic_cert.initial_lo), fraction_text(cubic_cert.initial_hi)],
            "steps": cubic_cert.steps,
            "branch_code": cubic_cert.branch_code,
            "branches": list(cubic_cert.branches),
            "final": [fraction_text(cubic_cert.final_lo), fraction_text(cubic_cert.final_hi)],
            "verified": verify_cubic_bisection_certificate(cubic_cert),
        },
        "whole_path": {
            "base": path.base,
            "horizon": path.horizon,
            "least_code": path.code,
            "states": list(path.states),
        },
        "stable_root_observation": {
            "valid_certificates": len(certs),
            "sum": fraction_text(observer[0]),
            "product": fraction_text(observer[1]),
            "sum_squares": fraction_text(observer[2]),
        },
        "height_bounded_curve": {
            "curve": "y^2 = x^3 - x + 1",
            "height": 12,
            "points": [list(p) for p in points],
            "verified_complete_inside_box": verify_bounded_curve_list(12, points),
            "warning": "This certifies completeness only inside the supplied height box.",
        },
    }


if __name__ == "__main__":
    import json

    print(json.dumps(demo_payload(), indent=2, sort_keys=True))
