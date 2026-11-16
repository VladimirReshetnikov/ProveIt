#!/usr/bin/env python3
"""Exact finite reference implementation for the iPRA framework report.

This program uses only Python's standard library and exact integer/Fraction
arithmetic.  It checks finite instances of the definitions in the report; it
is not an iPRA proof checker and it does not replace the universal human
proofs or the planned Lean Prf/PRAAx derivations.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt
from typing import Callable, Dict, Generic, Hashable, Iterable, List, Mapping, Optional, Sequence, Set, Tuple, TypeVar

A = TypeVar("A", bound=Hashable)
S = TypeVar("S")
O = TypeVar("O")


def all_below(n: int, pred: Callable[[int], bool]) -> bool:
    """Finite universal Boolean fold."""
    if n < 0:
        raise ValueError("bound must be nonnegative")
    acc = True
    for i in range(n):
        acc = acc and bool(pred(i))
    return acc


def any_below(n: int, pred: Callable[[int], bool]) -> bool:
    """Finite existential Boolean fold."""
    if n < 0:
        raise ValueError("bound must be nonnegative")
    acc = False
    for i in range(n):
        acc = acc or bool(pred(i))
    return acc


def least_below(n: int, pred: Callable[[int], bool]) -> int:
    """Least witness below n, with n as the no-witness sentinel."""
    if n < 0:
        raise ValueError("bound must be nonnegative")
    for i in range(n):
        if pred(i):
            return i
    return n


@dataclass(frozen=True)
class TraceSystem(Generic[S]):
    """Finite semantic model of the proof-producing trace interface."""

    good: Callable[[int], bool]
    init: Callable[[int], S]
    bound: Callable[[int], int]
    step: Callable[[int, S, int], S]
    invariant: Callable[[int, S, int], bool]
    accept: Callable[[S, int], bool]

    def run(self, u: int) -> List[S]:
        b = self.bound(u)
        if b < 0:
            raise ValueError("trace bound must be nonnegative")
        states = [self.init(u)]
        for i in range(b):
            states.append(self.step(i, states[-1], u))
        return states

    def local_obligations_hold(self, u: int) -> bool:
        """Check base, every concrete step, and the final implication."""
        states = self.run(u)
        if not self.good(u):
            return True
        if not self.invariant(0, states[0], u):
            return False
        for i in range(self.bound(u)):
            if not self.invariant(i, states[i], u):
                return False
            if not self.invariant(i + 1, states[i + 1], u):
                return False
        return (not self.invariant(self.bound(u), states[-1], u)) or self.accept(states[-1], u)

    def reflected_result(self, u: int) -> bool:
        states = self.run(u)
        return (not self.good(u)) or self.accept(states[-1], u)


def finite_sum_trace(values: Sequence[int]) -> TraceSystem[int]:
    prefix = [0]
    for x in values:
        prefix.append(prefix[-1] + x)

    return TraceSystem(
        good=lambda _u: True,
        init=lambda _u: 0,
        bound=lambda _u: len(values),
        step=lambda i, state, _u: state + values[i],
        invariant=lambda i, state, _u: state == prefix[i],
        accept=lambda state, _u: state == sum(values),
    )


@dataclass(frozen=True)
class LayeredRelation(Generic[A, O]):
    """A finite layered relation with exact observations."""

    candidates: Callable[[int], Sequence[A]]
    good: Callable[[int, A], bool]
    compat: Callable[[int, A, A], bool]
    observation: Callable[[int, A], O]

    def good_candidates(self, level: int) -> Tuple[A, ...]:
        return tuple(a for a in self.candidates(level) if self.good(level, a))

    def backward_viable(self, horizon: int) -> Dict[int, Set[A]]:
        if horizon < 0:
            raise ValueError("horizon must be nonnegative")
        back: Dict[int, Set[A]] = {horizon: set(self.good_candidates(horizon))}
        for k in range(horizon - 1, -1, -1):
            next_nodes = back[k + 1]
            back[k] = {
                a
                for a in self.good_candidates(k)
                if any(self.compat(k, a, b) for b in next_nodes)
            }
        return back

    def forward_reachable(self, horizon: int) -> Dict[int, Set[A]]:
        if horizon < 0:
            raise ValueError("horizon must be nonnegative")
        reach: Dict[int, Set[A]] = {0: set(self.good_candidates(0))}
        for k in range(horizon):
            prev = reach[k]
            reach[k + 1] = {
                b
                for b in self.good_candidates(k + 1)
                if any(self.compat(k, a, b) for a in prev)
            }
        return reach

    def full_viable(self, horizon: int) -> Dict[int, Set[A]]:
        reach = self.forward_reachable(horizon)
        back = self.backward_viable(horizon)
        return {k: reach[k] & back[k] for k in range(horizon + 1)}

    def viable_from(self, level: int, depth: int, a: A) -> bool:
        """Recursive definition Viable(level, depth, a)."""
        if depth < 0:
            raise ValueError("depth must be nonnegative")
        if not self.good(level, a):
            return False
        if depth == 0:
            return True
        return any(
            self.compat(level, a, b) and self.viable_from(level + 1, depth - 1, b)
            for b in self.good_candidates(level + 1)
        )

    def least_path_from(self, level: int, depth: int, a: A) -> Tuple[A, ...]:
        if not self.viable_from(level, depth, a):
            raise ValueError("initial candidate is not viable to requested depth")
        path: List[A] = [a]
        current = a
        for j in range(depth):
            remaining = depth - j - 1
            options = [
                b
                for b in self.good_candidates(level + j + 1)
                if self.compat(level + j, current, b)
                and self.viable_from(level + j + 1, remaining, b)
            ]
            if not options:
                raise AssertionError("viability recursion promised a successor")
            current = min(options)
            path.append(current)
        return tuple(path)

    def least_full_viable(self, horizon: int, level: int) -> A:
        if not (0 <= level <= horizon):
            raise ValueError("level must lie in the horizon")
        cloud = self.full_viable(horizon)[level]
        if not cloud:
            raise ValueError("full-viable cloud is empty")
        return min(cloud)

    def least_path_through(self, horizon: int, level: int, node: A) -> Tuple[A, ...]:
        """Construct the least complete path through a full-viable node."""
        if not (0 <= level <= horizon):
            raise ValueError("level must lie in the horizon")
        full = self.full_viable(horizon)
        if node not in full[level]:
            raise ValueError("node is not full viable")

        prefix: List[A] = [node]
        current = node
        for k in range(level - 1, -1, -1):
            options = [
                a for a in full[k] if self.compat(k, a, current)
            ]
            if not options:
                raise AssertionError("full viability promised a predecessor")
            current = min(options)
            prefix.append(current)
        prefix.reverse()

        suffix: List[A] = []
        current = node
        back = self.backward_viable(horizon)
        for k in range(level, horizon):
            options = [
                b
                for b in back[k + 1]
                if self.good(k + 1, b) and self.compat(k, current, b)
            ]
            if not options:
                raise AssertionError("full viability promised a successor")
            current = min(options)
            suffix.append(current)
        path = tuple(prefix + suffix)
        if len(path) != horizon + 1:
            raise AssertionError("constructed path has the wrong length")
        return path

    def path_ok(self, path: Sequence[A]) -> bool:
        if not path:
            return False
        for k, a in enumerate(path):
            if not self.good(k, a):
                return False
            if k + 1 < len(path) and not self.compat(k, a, path[k + 1]):
                return False
        return True


def verify_shrinking_bound(
    relation: LayeredRelation[A, Fraction],
    horizon: Callable[[int], int],
    epsilon: Callable[[int], Fraction],
    delta: Callable[[int], Fraction],
    max_level: int,
) -> Mapping[str, object]:
    """Check the exact finite instances of the shrinking-viability proof."""
    if max_level < 0:
        raise ValueError("max_level must be nonnegative")

    hs = [horizon(k) for k in range(max_level + 1)]
    if any(hs[k] < k for k in range(max_level + 1)):
        raise AssertionError("horizon must dominate the level")
    if any(hs[k] > hs[k + 1] for k in range(max_level)):
        raise AssertionError("horizon must be nondecreasing")

    selected: List[A] = []
    observations: List[Fraction] = []
    cloud_sizes: List[int] = []

    for k, h in enumerate(hs):
        full = relation.full_viable(h)
        cloud = full[k]
        if not cloud:
            raise AssertionError(f"empty viable cloud at level {k}")
        values = [relation.observation(k, a) for a in cloud]
        diameter = max(values) - min(values)
        if diameter > epsilon(k):
            raise AssertionError(
                f"cloud diameter {diameter} exceeds epsilon {epsilon(k)} at {k}"
            )
        a = min(cloud)
        selected.append(a)
        observations.append(relation.observation(k, a))
        cloud_sizes.append(len(cloud))

    checks = 0
    worst_slack: Optional[Fraction] = None
    for k in range(max_level + 1):
        for ell in range(k, max_level + 1):
            lhs = abs(observations[k] - observations[ell])
            rhs = epsilon(k) + sum((delta(j) for j in range(k, ell)), Fraction(0))
            if lhs > rhs:
                raise AssertionError(
                    f"shrinking bound fails at ({k},{ell}): {lhs} > {rhs}"
                )

            # Mirror the human proof: take a path through the later selector,
            # truncate it, and check the ancestor is viable at the earlier
            # horizon.
            later_path = relation.least_path_through(hs[ell], ell, selected[ell])
            ancestor = later_path[k]
            if ancestor not in relation.full_viable(hs[k])[k]:
                raise AssertionError("truncated ancestor is not full viable")
            edge_motion = sum(
                (
                    abs(
                        relation.observation(j, later_path[j])
                        - relation.observation(j + 1, later_path[j + 1])
                    )
                    for j in range(k, ell)
                ),
                Fraction(0),
            )
            if edge_motion > sum((delta(j) for j in range(k, ell)), Fraction(0)):
                raise AssertionError("path exceeds declared edge budget")
            slack = rhs - lhs
            worst_slack = slack if worst_slack is None else min(worst_slack, slack)
            checks += 1

    return {
        "levels": max_level + 1,
        "horizons": hs,
        "cloud_sizes": cloud_sizes,
        "selected_codes": selected,
        "selected_observations": [str(x) for x in observations],
        "pair_checks": checks,
        "minimum_slack": str(worst_slack if worst_slack is not None else Fraction(0)),
    }


def sqrt2_relation() -> LayeredRelation[int, Fraction]:
    """Relational rational-grid approximation used in the report."""

    def denominator(k: int) -> int:
        return 2 ** (k + 4)

    def candidates(k: int) -> Sequence[int]:
        d = denominator(k)
        # Solve the exact residual interval before enumeration.  Since d^2 is
        # divisible by 2^k, both endpoints are integers.
        radius_sq = (d * d) // (2**k)
        lower_sq = 2 * d * d - radius_sq
        upper_sq = 2 * d * d + radius_sq
        lo = isqrt(lower_sq - 1) + 1
        hi = isqrt(upper_sq)
        return range(max(d, lo), min(2 * d, hi) + 1)

    def obs(k: int, a: int) -> Fraction:
        return Fraction(a, denominator(k))

    def good(k: int, a: int) -> bool:
        q = obs(k, a)
        return Fraction(1) <= q <= Fraction(2) and abs(q * q - 2) <= Fraction(1, 2**k)

    def compat(k: int, a: int, b: int) -> bool:
        return abs(obs(k, a) - obs(k + 1, b)) <= 3 * Fraction(1, 2**k)

    return LayeredRelation(candidates=candidates, good=good, compat=compat, observation=obs)


def enumerate_bounded(
    codes: Iterable[A], predicate: Callable[[A], bool]
) -> Tuple[A, ...]:
    """Finite complete list below an externally supplied code bound."""
    return tuple(x for x in codes if predicate(x))


def maximum_height(items: Sequence[A], height: Callable[[A], int]) -> int:
    return max((height(x) for x in items), default=0)


def demo_results() -> Mapping[str, object]:
    trace = finite_sum_trace([3, -2, 5, 7, -4])
    trace_states = trace.run(0)
    if not trace.local_obligations_hold(0) or not trace.reflected_result(0):
        raise AssertionError("finite-sum trace check failed")

    relation = sqrt2_relation()
    shrinking = verify_shrinking_bound(
        relation=relation,
        horizon=lambda k: k + 3,
        epsilon=lambda k: Fraction(1, 2**k),
        delta=lambda k: 3 * Fraction(1, 2**k),
        max_level=8,
    )

    # A small dead-end relation demonstrates why local goodness is not enough.
    dead_end = LayeredRelation[int, int](
        candidates=lambda k: {0: [0, 1], 1: [0, 1], 2: [0]}.get(k, []),
        good=lambda _k, _a: True,
        compat=lambda k, a, b: (
            (k == 0 and ((a, b) in {(0, 0), (1, 1)}))
            or (k == 1 and (a, b) == (1, 0))
        ),
        observation=lambda _k, a: a,
    )
    back = dead_end.backward_viable(2)
    if 0 in back[0] or 1 not in back[0]:
        raise AssertionError("backward viability did not remove the dead end")
    path = dead_end.least_path_from(0, 2, 1)
    if path != (1, 1, 0):
        raise AssertionError(f"unexpected viable path: {path}")

    points = enumerate_bounded(range(-12, 13), lambda x: x * x == 9)
    height_bound = maximum_height(points, abs)
    if set(points) != {-3, 3} or height_bound != 3:
        raise AssertionError("bounded enumeration/height example failed")

    return {
        "status": "all exact finite checks passed",
        "scope": "reference checks only; not an iPRA proof checker",
        "finite_sum_trace": {
            "states": trace_states,
            "result": trace_states[-1],
            "expected": sum([3, -2, 5, 7, -4]),
        },
        "dead_end_viability": {
            "backward_sets": {str(k): sorted(v) for k, v in back.items()},
            "least_path": list(path),
        },
        "shrinking_sqrt2": shrinking,
        "height_list": {
            "solutions_below_bound": list(points),
            "recovered_height_bound": height_bound,
        },
    }


if __name__ == "__main__":
    import json

    print(json.dumps(demo_results(), indent=2, sort_keys=True))
