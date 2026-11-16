#!/usr/bin/env python3
"""Exact reference algorithms for the CFP contract-DAG report.

This module is deliberately small and uses only Python's standard library.
It is semantic test code, not an iPRA proof checker.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import argparse
import json
from pathlib import Path
from typing import Callable, Iterable, Sequence


def pair(a: int, b: int) -> int:
    """2-adic pairing: <a,b> = 2^a (2b+1)-1."""
    if a < 0 or b < 0:
        raise ValueError("pair arguments must be natural numbers")
    return (1 << a) * (2 * b + 1) - 1


def unpair(n: int) -> tuple[int, int]:
    """Inverse of pair."""
    if n < 0:
        raise ValueError("code must be a natural number")
    m = n + 1
    a = 0
    while m % 2 == 0:
        a += 1
        m //= 2
    b = (m - 1) // 2
    return a, b


def all_below(bound: int, pred: Callable[[int], bool]) -> bool:
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    acc = True
    for i in range(bound):
        acc = acc and bool(pred(i))
    return acc


def any_below(bound: int, pred: Callable[[int], bool]) -> bool:
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    acc = False
    for i in range(bound):
        acc = acc or bool(pred(i))
    return acc


def first_true(bound: int, pred: Callable[[int], bool]) -> int:
    """Return the first witness below bound, or bound as a sentinel."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    witness = bound
    for i in range(bound):
        if witness == bound and pred(i):
            witness = i
    return witness


@dataclass(frozen=True)
class EdgeDemand:
    parent: int
    offset: int = 0
    scale: int = 1

    def __call__(self, request: int) -> int:
        if request < 0 or self.offset < 0 or self.scale < 0:
            raise ValueError("requests, offsets, and scales must be natural")
        return self.scale * request + self.offset


def reverse_demands(
    parents: Sequence[Sequence[EdgeDemand]],
    external_requests: Sequence[int],
) -> list[int]:
    """Propagate demands backward in a topologically numbered DAG.

    Every parent index must be smaller than its child index.
    """
    n = len(parents)
    if len(external_requests) != n:
        raise ValueError("request vector length mismatch")
    req = list(external_requests)
    if any(q < 0 for q in req):
        raise ValueError("requests must be nonnegative")
    for child in reversed(range(n)):
        for edge in parents[child]:
            if not 0 <= edge.parent < child:
                raise ValueError("graph is not topologically ordered")
            req[edge.parent] = max(req[edge.parent], edge(req[child]))
    return req


def demands_adequate(
    parents: Sequence[Sequence[EdgeDemand]], req: Sequence[int]
) -> bool:
    return all(
        req[edge.parent] >= edge(req[child])
        for child in range(len(parents))
        for edge in parents[child]
    )


def coherent_path(
    candidates: Sequence[Sequence[int]],
    compat: Callable[[int, int, int], bool],
) -> list[int]:
    """Choose a least finite compatible path by backward viability."""
    if not candidates or any(len(level) == 0 for level in candidates):
        raise ValueError("all candidate levels must be nonempty")
    kmax = len(candidates) - 1
    viable: list[set[int]] = [set() for _ in candidates]
    viable[kmax] = set(candidates[kmax])
    for k in reversed(range(kmax)):
        viable[k] = {
            c
            for c in candidates[k]
            if any(compat(k, c, d) and d in viable[k + 1]
                   for d in candidates[k + 1])
        }
    if not viable[0]:
        raise ValueError("no viable root candidate")
    path = [min(viable[0])]
    for k in range(kmax):
        choices = [
            d
            for d in candidates[k + 1]
            if compat(k, path[-1], d) and d in viable[k + 1]
        ]
        if not choices:
            raise AssertionError("viability invariant broken")
        path.append(min(choices))
    return path


def check_coherent_path(
    path: Sequence[int],
    candidates: Sequence[Sequence[int]],
    compat: Callable[[int, int, int], bool],
) -> bool:
    return (
        len(path) == len(candidates)
        and all(path[k] in candidates[k] for k in range(len(path)))
        and all(compat(k, path[k], path[k + 1])
                for k in range(len(path) - 1))
    )


def gap_decide(approx: Fraction, error: Fraction, delta: Fraction) -> str:
    """Decide zero versus delta-apart under the documented promise.

    The caller must separately verify the promise x=0 or |x|>=delta and
    |x-approx|<=error.  This function checks only the numerical preconditions.
    """
    if not delta > 0:
        raise ValueError("delta must be positive")
    if not 0 <= error < delta / 4:
        raise ValueError("error must be less than delta/4")
    return "zero" if abs(approx) < delta / 2 else "apart"


def verify_gap_decision(
    x: Fraction, approx: Fraction, error: Fraction, delta: Fraction
) -> bool:
    if abs(x - approx) > error:
        return False
    if not (x == 0 or abs(x) >= delta):
        return False
    decision = gap_decide(approx, error, delta)
    return (decision == "zero" and x == 0) or (
        decision == "apart" and abs(x) >= delta
    )


def bounded_enumerate(bound: int, pred: Callable[[int], bool]) -> list[int]:
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return [x for x in range(bound + 1) if pred(x)]


def list_is_complete_below(
    values: Sequence[int], bound: int, pred: Callable[[int], bool]
) -> bool:
    value_set = set(values)
    sound = all(0 <= x <= bound and pred(x) for x in values)
    complete = all((not pred(x)) or x in value_set for x in range(bound + 1))
    return sound and complete


def cubic_f(x: Fraction, y: Fraction) -> Fraction:
    return y * y * y + y - x


def cubic_bisect(x: Fraction, steps: int) -> tuple[Fraction, Fraction]:
    if not Fraction(0) <= x <= Fraction(1):
        raise ValueError("x must lie in [0,1]")
    if steps < 0:
        raise ValueError("steps must be nonnegative")
    lo, hi = Fraction(0), Fraction(1)
    for _ in range(steps):
        mid = (lo + hi) / 2
        if cubic_f(x, mid) <= 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


def verify_cubic_interval(
    x: Fraction, steps: int, lo: Fraction, hi: Fraction
) -> bool:
    if not (Fraction(0) <= lo <= hi <= Fraction(1)):
        return False
    if cubic_f(x, lo) > 0 or cubic_f(x, hi) < 0:
        return False
    return hi - lo == Fraction(1, 1 << steps)


def cubic_certificate(x: Fraction, steps: int) -> dict[str, str | int]:
    lo, hi = cubic_bisect(x, steps)
    center = (lo + hi) / 2
    residual = abs(cubic_f(x, center))
    bound = Fraction(4, 1 << steps)
    if not verify_cubic_interval(x, steps, lo, hi):
        raise AssertionError("bisection invariant failed")
    if residual > bound:
        raise AssertionError("residual bound failed")
    return {
        "steps": steps,
        "x": str(x),
        "lo": str(lo),
        "hi": str(hi),
        "center": str(center),
        "width": str(hi - lo),
        "residual": str(residual),
        "residual_bound": str(bound),
    }


def cubic_quantitative_unique(
    x: Fraction, p: Fraction, q: Fraction, eps: Fraction
) -> bool:
    if not (Fraction(0) <= p <= 1 and Fraction(0) <= q <= 1):
        return False
    if abs(cubic_f(x, p)) > eps or abs(cubic_f(x, q)) > eps:
        return False
    return abs(p - q) <= 2 * eps


def parse_fraction(value: str | int) -> Fraction:
    return Fraction(value)


def validate_json_certificate(data: dict) -> dict:
    cubic = data["cubic"]
    x = Fraction(cubic["x_num"], cubic["x_den"])
    cubic_result = cubic_certificate(x, int(cubic["steps"]))

    graph = data["dag"]
    n = int(graph["nodes"])
    parents: list[list[EdgeDemand]] = [[] for _ in range(n)]
    for item in graph["edges"]:
        parent = int(item["parent"])
        child = int(item["child"])
        parents[child].append(
            EdgeDemand(
                parent=parent,
                offset=int(item.get("offset", 0)),
                scale=int(item.get("scale", 1)),
            )
        )
    req = reverse_demands(parents, [int(q) for q in graph["external"]])
    if not demands_adequate(parents, req):
        raise AssertionError("reverse demand adequacy failed")

    rel = data["relational"]
    levels = [[int(x) for x in level] for level in rel["levels"]]
    allowed = {
        (int(a), int(b), int(c))
        for a, b, c in rel["compatible"]
    }
    compat = lambda k, c, d: (k, c, d) in allowed
    path = coherent_path(levels, compat)
    if not check_coherent_path(path, levels, compat):
        raise AssertionError("coherent path failed")

    return {
        "cubic": cubic_result,
        "reverse_requests": req,
        "coherent_path": path,
        "status": "all certificate checks passed",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "certificate",
        nargs="?",
        default="../examples/framework_certificate.json",
        help="JSON certificate file",
    )
    args = parser.parse_args()
    data = json.loads(Path(args.certificate).read_text(encoding="utf-8"))
    print(json.dumps(validate_json_certificate(data), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
