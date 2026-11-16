#!/usr/bin/env python3
"""Exact finite reference algorithms for SCOPE-iPRA.

This module is executable evidence for the finite algorithms described in the
paper.  It is not an object-language proof checker and it does not replace the
Lean `Prf PRAAx` derivations required by the framework.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import argparse
import json
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping, Sequence


class EscapeMode(str, Enum):
    """How a certificate may cross a proof boundary."""

    PRIVATE = "private"
    EXISTENTIAL = "existential"
    STABLE = "stable"
    CANONICAL = "canonical"
    RESIDUAL = "residual"


class BForm:
    """A tiny executable model of fixed bounded formulas."""

    def eval(self, env: tuple[int, ...]) -> bool:
        raise NotImplementedError


@dataclass(frozen=True)
class Eq(BForm):
    left: Callable[[tuple[int, ...]], int]
    right: Callable[[tuple[int, ...]], int]

    def eval(self, env: tuple[int, ...]) -> bool:
        return self.left(env) == self.right(env)


@dataclass(frozen=True)
class And(BForm):
    left: BForm
    right: BForm

    def eval(self, env: tuple[int, ...]) -> bool:
        return self.left.eval(env) and self.right.eval(env)


@dataclass(frozen=True)
class Or(BForm):
    left: BForm
    right: BForm

    def eval(self, env: tuple[int, ...]) -> bool:
        return self.left.eval(env) or self.right.eval(env)


@dataclass(frozen=True)
class Not(BForm):
    body: BForm

    def eval(self, env: tuple[int, ...]) -> bool:
        return not self.body.eval(env)


@dataclass(frozen=True)
class Imp(BForm):
    left: BForm
    right: BForm

    def eval(self, env: tuple[int, ...]) -> bool:
        return (not self.left.eval(env)) or self.right.eval(env)


@dataclass(frozen=True)
class AllLt(BForm):
    bound: Callable[[tuple[int, ...]], int]
    body: BForm

    def eval(self, env: tuple[int, ...]) -> bool:
        b = checked_nat(self.bound(env), "bounded universal bound")
        return all(self.body.eval((i,) + env) for i in range(b))


@dataclass(frozen=True)
class ExLt(BForm):
    bound: Callable[[tuple[int, ...]], int]
    body: BForm

    def eval(self, env: tuple[int, ...]) -> bool:
        b = checked_nat(self.bound(env), "bounded existential bound")
        return any(self.body.eval((i,) + env) for i in range(b))


def checked_nat(value: int, what: str = "value") -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{what} must be a natural number, got {value!r}")
    return value


def bool_bit(value: bool) -> int:
    return 1 if value else 0


def compile_bit(formula: BForm, env: Sequence[int]) -> int:
    """Reference Boolean evaluator corresponding to the reflected bit."""

    return bool_bit(formula.eval(tuple(checked_nat(x, "environment entry") for x in env)))


def least_accepted(bound: int, accepted: Callable[[int], bool]) -> tuple[int, bool]:
    """Least accepted code below `bound`, with `bound` as the failure sentinel."""

    bound = checked_nat(bound, "search bound")
    for code in range(bound):
        if accepted(code):
            return code, True
    return bound, False


def mixed_radix_encode(digits: Sequence[int], caps: Sequence[int]) -> int:
    """Encode 0 <= digit[i] <= cap[i] in one natural number."""

    if len(digits) != len(caps):
        raise ValueError("digits and caps must have equal length")
    code = 0
    multiplier = 1
    for i, (digit, cap) in enumerate(zip(digits, caps, strict=True)):
        digit = checked_nat(digit, f"digit {i}")
        cap = checked_nat(cap, f"cap {i}")
        if digit > cap:
            raise ValueError(f"digit {i}={digit} exceeds cap {cap}")
        code += digit * multiplier
        multiplier *= cap + 1
    return code


def mixed_radix_decode(code: int, caps: Sequence[int]) -> tuple[int, ...]:
    code = checked_nat(code, "mixed-radix code")
    digits: list[int] = []
    remaining = code
    capacity = 1
    for i, cap in enumerate(caps):
        cap = checked_nat(cap, f"cap {i}")
        base = cap + 1
        digits.append(remaining % base)
        remaining //= base
        capacity *= base
    if remaining:
        raise ValueError(f"code {code} is outside capacity {capacity}")
    return tuple(digits)


def product_capacity(caps: Sequence[int]) -> int:
    result = 1
    for i, cap in enumerate(caps):
        result *= checked_nat(cap, f"cap {i}") + 1
    return result


def componentwise_le(left: Sequence[int], right: Sequence[int]) -> bool:
    if len(left) != len(right):
        raise ValueError("vectors must have equal length")
    return all(a <= b for a, b in zip(left, right, strict=True))


def join(left: Sequence[int], right: Sequence[int]) -> tuple[int, ...]:
    if len(left) != len(right):
        raise ValueError("vectors must have equal length")
    return tuple(max(a, b) for a, b in zip(left, right, strict=True))


def demand_closure(
    caps: Sequence[int],
    transformer: Callable[[tuple[int, ...]], Sequence[int]],
    start: Sequence[int] | None = None,
) -> dict[str, Any]:
    """Least capped prefixed point of d |-> d join F(d).

    Correctness assumes `transformer` is monotone on the capped product.  The
    routine validates range preservation and uses the theorem's explicit rank
    budget sum(caps).  It returns every iterate as finite evidence.
    """

    caps_t = tuple(checked_nat(c, f"cap {i}") for i, c in enumerate(caps))
    if start is None:
        current = tuple(0 for _ in caps_t)
    else:
        if len(start) != len(caps_t):
            raise ValueError("start and caps must have equal length")
        current = tuple(checked_nat(x, f"start {i}") for i, x in enumerate(start))
        if not componentwise_le(current, caps_t):
            raise ValueError("start exceeds caps")

    history = [current]
    budget = sum(caps_t) + 1  # one extra attempted step exposes fixedness
    for _ in range(budget):
        raw = tuple(checked_nat(x, "transformer output") for x in transformer(current))
        if len(raw) != len(caps_t):
            raise ValueError("transformer returned wrong dimension")
        if not componentwise_le(raw, caps_t):
            raise ValueError(f"transformer output {raw} exceeds caps {caps_t}")
        nxt = join(current, raw)
        history.append(nxt)
        if nxt == current:
            return {
                "fixed_point": list(current),
                "iterations": len(history) - 2,
                "rank": sum(current),
                "rank_budget": sum(caps_t),
                "history": [list(v) for v in history],
            }
        current = nxt
    raise AssertionError("rank argument failed: no fixed point within explicit budget")


def check_monotone(
    caps: Sequence[int], transformer: Callable[[tuple[int, ...]], Sequence[int]]
) -> bool:
    """Exhaustive finite monotonicity check, intended only for small examples."""

    caps_t = tuple(checked_nat(c) for c in caps)
    capacity = product_capacity(caps_t)
    vectors = [mixed_radix_decode(code, caps_t) for code in range(capacity)]
    images = {v: tuple(transformer(v)) for v in vectors}
    for v in vectors:
        if len(images[v]) != len(caps_t) or not componentwise_le(images[v], caps_t):
            return False
    return all(
        not componentwise_le(v, w) or componentwise_le(images[v], images[w])
        for v in vectors
        for w in vectors
    )


@dataclass(frozen=True)
class ViabilityResult:
    path: tuple[Any, ...]
    viable_levels: tuple[tuple[Any, ...], ...]


def backward_viability(
    levels: Sequence[Sequence[Any]],
    valid: Callable[[int, Any], bool],
    compatible: Callable[[int, Any, Any], bool],
    key: Callable[[Any], Any] | None = None,
) -> ViabilityResult | None:
    """Choose the lexicographically least globally viable finite path."""

    if not levels:
        return ViabilityResult((), ())
    order_key = key or (lambda x: x)
    viable: list[set[Any]] = [set() for _ in levels]
    viable[-1] = {a for a in levels[-1] if valid(len(levels) - 1, a)}
    for i in range(len(levels) - 2, -1, -1):
        viable[i] = {
            a
            for a in levels[i]
            if valid(i, a)
            and any(compatible(i, a, b) for b in viable[i + 1])
        }
    if not viable[0]:
        return None
    path = [min(viable[0], key=order_key)]
    for i in range(len(levels) - 1):
        candidates = [b for b in viable[i + 1] if compatible(i, path[-1], b)]
        if not candidates:
            raise AssertionError("viability recurrence promised a continuation")
        path.append(min(candidates, key=order_key))
    return ViabilityResult(
        path=tuple(path),
        viable_levels=tuple(tuple(sorted(s, key=order_key)) for s in viable),
    )


def solve_forall_exists(
    x_bound: int,
    y_bound: Callable[[int], int],
    relation: Callable[[int, int], bool],
) -> dict[str, Any]:
    """Finite strategy certificate for forall x<x_bound, exists y<Y(x)."""

    x_bound = checked_nat(x_bound, "x bound")
    strategy: list[int] = []
    for x in range(x_bound):
        bound = checked_nat(y_bound(x), f"y bound at {x}")
        y, found = least_accepted(bound, lambda candidate: relation(x, candidate))
        if not found:
            return {
                "truth": False,
                "counterexample_x": x,
                "checked_y_bound": bound,
                "strategy": strategy,
            }
        strategy.append(y)
    return {"truth": True, "strategy": strategy}


def verify_forall_exists_strategy(
    strategy: Sequence[int],
    x_bound: int,
    y_bound: Callable[[int], int],
    relation: Callable[[int, int], bool],
) -> bool:
    if len(strategy) != x_bound:
        return False
    return all(0 <= strategy[x] < y_bound(x) and relation(x, strategy[x]) for x in range(x_bound))


def stable_observation(
    certificates: Iterable[Any],
    valid: Callable[[Any], bool],
    observe: Callable[[Any], Any],
) -> tuple[bool, Any | None]:
    """Check exact certificate-independence of a finite observation."""

    observations = [observe(c) for c in certificates if valid(c)]
    if not observations:
        return False, None
    first = observations[0]
    return all(o == first for o in observations), first


def diameter_bound(
    certificates: Iterable[Any],
    valid: Callable[[Any], bool],
    observe: Callable[[Any], int],
) -> int | None:
    observations = [observe(c) for c in certificates if valid(c)]
    if not observations:
        return None
    return max(observations) - min(observations)


def tree_error_bound(
    root: Any,
    parent: Mapping[Any, Any | None],
    edge_error: Mapping[Any, int],
) -> dict[Any, int]:
    """Accumulate nonnegative metric errors from a rooted finite tree."""

    if parent.get(root, None) is not None:
        raise ValueError("root must have no parent")
    memo: dict[Any, int] = {root: 0}
    visiting: set[Any] = set()

    def distance(node: Any) -> int:
        if node in memo:
            return memo[node]
        if node in visiting:
            raise ValueError("parent relation contains a cycle")
        visiting.add(node)
        if node not in parent or parent[node] is None:
            raise ValueError(f"node {node!r} is disconnected from root")
        p = parent[node]
        err = checked_nat(edge_error[node], f"edge error at {node!r}")
        result = distance(p) + err
        visiting.remove(node)
        memo[node] = result
        return result

    for node in parent:
        distance(node)
    return memo


def classify_escape(
    public_depends_on_certificate: bool,
    output_is_existential: bool = False,
    stable_observer_proved: bool = False,
    bounded_canonical_order: bool = False,
    producer_available: bool = True,
) -> EscapeMode:
    """Deterministic reference version of the SCOPE escape analysis."""

    if not producer_available:
        return EscapeMode.RESIDUAL
    if not public_depends_on_certificate:
        return EscapeMode.PRIVATE
    if output_is_existential:
        return EscapeMode.EXISTENTIAL
    if stable_observer_proved:
        return EscapeMode.STABLE
    if bounded_canonical_order:
        return EscapeMode.CANONICAL
    return EscapeMode.RESIDUAL


def build_demo() -> dict[str, Any]:
    caps = (5, 6, 5)

    def demands(d: tuple[int, ...]) -> tuple[int, ...]:
        return (
            min(caps[0], d[1] + 1),
            min(caps[1], d[2] + 2),
            min(caps[2], d[0]),
        )

    closure = demand_closure(caps, demands)
    levels = ((0, 1), (0, 1), (0,))

    def compat(i: int, a: int, b: int) -> bool:
        edges = {
            0: {(0, 0), (1, 1)},
            1: {(1, 0)},
        }
        return (a, b) in edges[i]

    viability = backward_viability(levels, lambda _i, _a: True, compat)
    strategy = solve_forall_exists(
        6,
        lambda _x: 4,
        lambda x, y: (x + y) % 3 == 0,
    )
    parent = {"r": None, "a": "r", "b": "r", "c": "a"}
    errors = {"a": 2, "b": 1, "c": 3}
    return {
        "framework": "SCOPE-iPRA",
        "demand_closure": closure,
        "viability": None
        if viability is None
        else {
            "path": list(viability.path),
            "viable_levels": [list(v) for v in viability.viable_levels],
        },
        "forall_exists_strategy": strategy,
        "strategy_verified": verify_forall_exists_strategy(
            strategy.get("strategy", []),
            6,
            lambda _x: 4,
            lambda x, y: (x + y) % 3 == 0,
        ),
        "tree_error_bounds": tree_error_bound("r", parent, errors),
        "escape_examples": {
            "private": classify_escape(False).value,
            "existential": classify_escape(True, output_is_existential=True).value,
            "stable": classify_escape(True, stable_observer_proved=True).value,
            "canonical": classify_escape(True, bounded_canonical_order=True).value,
            "residual": classify_escape(True).value,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--demo", type=Path, help="write a deterministic demo JSON file")
    args = parser.parse_args()
    if args.demo:
        args.demo.parent.mkdir(parents=True, exist_ok=True)
        args.demo.write_text(json.dumps(build_demo(), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        print(json.dumps(build_demo(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
