"""Exact finite reference implementation for the KIFC-R report.

This module tests the finite algorithms used by the human proofs:
Boolean folds, the current least-zero search convention, bounded traces,
acyclic and capped-cyclic reverse demand, residual reachability, backward
viability, stable observers, shrinking budgets, guarded selection, rational
cubic bisection, and bounded-height enumeration.

It is deliberately *not* an iPRA proof checker.  Object-language soundness is
specified in the Lean blueprint and must ultimately produce ``Prf PRAAx``
derivations in the pinned ProveIt repository.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import (
    Callable,
    Generic,
    Hashable,
    Iterable,
    Mapping,
    Sequence,
    TypeVar,
)

T = TypeVar("T", bound=Hashable)
S = TypeVar("S")
P = TypeVar("P")
X = TypeVar("X", bound=Hashable)


def _require_nonnegative(value: int, name: str) -> None:
    if value < 0:
        raise ValueError(f"{name} must be nonnegative")


def bounded_all(bound: int, predicate: Callable[[int], bool]) -> bool:
    """Boolean universal fold over ``0 <= i < bound``."""
    _require_nonnegative(bound, "bound")
    accumulator = True
    for index in range(bound):
        accumulator = accumulator and bool(predicate(index))
    return accumulator


def bounded_any(bound: int, predicate: Callable[[int], bool]) -> bool:
    """Boolean existential fold over ``0 <= i < bound``."""
    _require_nonnegative(bound, "bound")
    accumulator = False
    for index in range(bound):
        accumulator = accumulator or bool(predicate(index))
    return accumulator


@dataclass(frozen=True)
class SearchResult:
    found: bool
    witness: int


def least_bounded(
    bound: int,
    predicate: Callable[[int], bool],
    *,
    default: int = 0,
) -> SearchResult:
    """Primitive-recursion-style least bounded search.

    The loop does not stop early: after the first hit it preserves the stored
    witness.  This mirrors the object-level ``(found,witness)`` recurrence.
    """
    _require_nonnegative(bound, "bound")
    found = False
    witness = default
    for index in range(bound):
        hit = bool(predicate(index))
        if (not found) and hit:
            found = True
            witness = index
    return SearchResult(found=found, witness=witness)


def search_invariant(
    bound: int,
    predicate: Callable[[int], bool],
    *,
    default: int = 0,
) -> bool:
    """Check the prefix invariant used in the least-search proof."""
    _require_nonnegative(bound, "bound")
    found = False
    witness = default
    for index in range(bound + 1):
        prefix = [j for j in range(index) if predicate(j)]
        if found != bool(prefix):
            return False
        if found:
            if witness != min(prefix):
                return False
            if not (0 <= witness < index and predicate(witness)):
                return False
            if any(predicate(j) for j in range(witness)):
                return False
        elif witness != default:
            return False
        if index == bound:
            break
        if (not found) and predicate(index):
            found = True
            witness = index
    return True


@dataclass(frozen=True)
class TraceCertificate(Generic[S]):
    states: tuple[S, ...]
    invariant_holds: bool
    terminal_holds: bool


def run_trace(
    init: S,
    step: Callable[[int, S], S],
    fuel: int,
    invariant: Callable[[int, S], bool],
    terminal: Callable[[S], bool],
) -> TraceCertificate[S]:
    """Execute a bounded recurrence and check its invariant at every time."""
    _require_nonnegative(fuel, "fuel")
    states: list[S] = [init]
    state = init
    invariant_holds = bool(invariant(0, state))
    for time in range(fuel):
        state = step(time, state)
        states.append(state)
        invariant_holds = invariant_holds and bool(invariant(time + 1, state))
    return TraceCertificate(
        states=tuple(states),
        invariant_holds=invariant_holds,
        terminal_holds=bool(terminal(state)),
    )


@dataclass(frozen=True)
class DemandEdge(Generic[P]):
    provider: str
    consumer: str
    transform: Callable[[int, P], int]


@dataclass(frozen=True)
class DemandGraph(Generic[P]):
    """A provider-before-consumer finite DAG."""

    nodes: tuple[str, ...]
    edges: tuple[DemandEdge[P], ...]

    def __post_init__(self) -> None:
        if len(set(self.nodes)) != len(self.nodes):
            raise ValueError("node names must be unique")
        position = {node: index for index, node in enumerate(self.nodes)}
        for edge in self.edges:
            if edge.provider not in position or edge.consumer not in position:
                raise ValueError(f"unknown endpoint in {edge!r}")
            if position[edge.provider] >= position[edge.consumer]:
                raise ValueError("provider must precede consumer")

    def reverse_demands(
        self,
        terminal: Mapping[str, int],
        params: P,
    ) -> dict[str, int]:
        request = {node: 0 for node in self.nodes}
        for node, value in terminal.items():
            if node not in request:
                raise ValueError(f"unknown terminal node {node!r}")
            _require_nonnegative(value, "terminal request")
            request[node] = max(request[node], value)

        outgoing: dict[str, list[DemandEdge[P]]] = {
            node: [] for node in self.nodes
        }
        for edge in self.edges:
            outgoing[edge.provider].append(edge)

        for provider in reversed(self.nodes):
            needed = request[provider]
            for edge in outgoing[provider]:
                transformed = edge.transform(request[edge.consumer], params)
                _require_nonnegative(transformed, "transformed demand")
                needed = max(needed, transformed)
            request[provider] = needed
        return request

    def satisfies(
        self,
        request: Mapping[str, int],
        terminal: Mapping[str, int],
        params: P,
    ) -> bool:
        if any(node not in request for node in self.nodes):
            return False
        if any(request.get(node, -1) < value for node, value in terminal.items()):
            return False
        return all(
            request[edge.provider]
            >= edge.transform(request[edge.consumer], params)
            for edge in self.edges
        )

    def componentwise_least_against(
        self,
        computed: Mapping[str, int],
        candidate: Mapping[str, int],
        terminal: Mapping[str, int],
        params: P,
    ) -> bool:
        if not self.satisfies(candidate, terminal, params):
            return False
        return all(computed[node] <= candidate[node] for node in self.nodes)


@dataclass(frozen=True)
class FiniteRelationTower(Generic[T]):
    levels: tuple[tuple[T, ...], ...]
    edge: Callable[[int, T, T], bool]
    terminal: Callable[[T], bool] = lambda _x: True
    valid: Callable[[int, T], bool] = lambda _i, _x: True

    def __post_init__(self) -> None:
        if not self.levels:
            raise ValueError("tower must have at least one level")
        for level in self.levels:
            if len(set(level)) != len(level):
                raise ValueError("candidates in a level must be unique")

    def _check_horizon(self, horizon: int) -> None:
        if not 0 <= horizon < len(self.levels):
            raise ValueError("horizon outside tower")

    def viable_sets(self, horizon: int) -> tuple[frozenset[T], ...]:
        """Backward viability through ``horizon`` inclusive."""
        self._check_horizon(horizon)
        viable: list[set[T]] = [set() for _ in range(horizon + 1)]
        for candidate in self.levels[horizon]:
            if self.valid(horizon, candidate) and self.terminal(candidate):
                viable[horizon].add(candidate)
        for level in range(horizon - 1, -1, -1):
            for candidate in self.levels[level]:
                if not self.valid(level, candidate):
                    continue
                if any(
                    self.edge(level, candidate, nxt)
                    for nxt in viable[level + 1]
                ):
                    viable[level].add(candidate)
        return tuple(frozenset(row) for row in viable)

    def brute_paths(
        self,
        start_level: int,
        horizon: int,
        start: T | None = None,
    ) -> tuple[tuple[T, ...], ...]:
        self._check_horizon(horizon)
        if not 0 <= start_level <= horizon:
            raise ValueError("invalid start level")
        rows: Sequence[Sequence[T]] = self.levels[start_level : horizon + 1]
        answer: list[tuple[T, ...]] = []
        for path in product(*rows):
            if start is not None and path[0] != start:
                continue
            if any(
                not self.valid(start_level + offset, candidate)
                for offset, candidate in enumerate(path)
            ):
                continue
            if not self.terminal(path[-1]):
                continue
            if all(
                self.edge(start_level + offset, path[offset], path[offset + 1])
                for offset in range(len(path) - 1)
            ):
                answer.append(tuple(path))
        return tuple(answer)

    def viability_matches_paths(self, horizon: int) -> bool:
        viable = self.viable_sets(horizon)
        for level in range(horizon + 1):
            for candidate in self.levels[level]:
                has_path = bool(self.brute_paths(level, horizon, candidate))
                if ((candidate in viable[level]) != has_path):
                    return False
        return True

    def least_viable_path(
        self,
        horizon: int,
        *,
        start_level: int = 0,
        key: Callable[[T], object] | None = None,
    ) -> tuple[T, ...]:
        self._check_horizon(horizon)
        if not 0 <= start_level <= horizon:
            raise ValueError("invalid start level")
        order = key or (lambda value: value)
        viable = self.viable_sets(horizon)
        starts = sorted(viable[start_level], key=order)
        if not starts:
            raise ValueError("no viable start candidate")
        path: list[T] = [starts[0]]
        for level in range(start_level, horizon):
            successors = sorted(
                (
                    candidate
                    for candidate in viable[level + 1]
                    if self.edge(level, path[-1], candidate)
                ),
                key=order,
            )
            if not successors:
                raise AssertionError("viability promised a successor")
            path.append(successors[0])
        return tuple(path)

    def path_is_valid(self, start_level: int, path: Sequence[T]) -> bool:
        if not path:
            return False
        if start_level < 0 or start_level + len(path) > len(self.levels):
            return False
        for offset, candidate in enumerate(path):
            level = start_level + offset
            if candidate not in self.levels[level] or not self.valid(level, candidate):
                return False
        if not self.terminal(path[-1]):
            return False
        return all(
            self.edge(start_level + offset, path[offset], path[offset + 1])
            for offset in range(len(path) - 1)
        )


def stable_observer(
    candidates: Iterable[T],
    *,
    valid: Callable[[T], bool],
    observe: Callable[[T], X],
    key: Callable[[T], object] | None = None,
) -> X:
    """Select a least valid candidate and verify exact observer stability."""
    order = key or (lambda value: value)
    valid_candidates = sorted((c for c in candidates if valid(c)), key=order)
    if not valid_candidates:
        raise ValueError("relation has no valid candidate")
    observations = [observe(candidate) for candidate in valid_candidates]
    if any(value != observations[0] for value in observations[1:]):
        raise ValueError("observer is not exact-stable")
    return observations[0]


def observation_diameter(
    candidates: Iterable[T],
    *,
    valid: Callable[[T], bool],
    observe: Callable[[T], Fraction],
) -> Fraction:
    values = [observe(candidate) for candidate in candidates if valid(candidate)]
    if not values:
        raise ValueError("relation has no valid candidate")
    return max(values) - min(values)


def adjacent_choice_bound(
    chosen_left: Fraction,
    chosen_right: Fraction,
    edge_left: Fraction,
    edge_right: Fraction,
    left_diameter: Fraction,
    motion: Fraction,
    right_diameter: Fraction,
) -> bool:
    """Check the three-term cloud/edge/cloud estimate."""
    if abs(chosen_left - edge_left) > left_diameter:
        return False
    if abs(edge_left - edge_right) > motion:
        return False
    if abs(edge_right - chosen_right) > right_diameter:
        return False
    return abs(chosen_left - chosen_right) <= (
        left_diameter + motion + right_diameter
    )


def tail_budget(
    diameter: Callable[[int], Fraction],
    motion: Callable[[int], Fraction],
    start: int,
    stop: int,
) -> Fraction:
    """Finite sum of ``delta_q + mu_q + delta_{q+1}``."""
    if not 0 <= start <= stop:
        raise ValueError("invalid tail interval")
    total = Fraction(0)
    for level in range(start, stop):
        total += diameter(level) + motion(level) + diameter(level + 1)
    return total


def guarded_argmin(
    approximations: Sequence[Fraction],
    error: Fraction,
    *,
    gap: Fraction,
) -> int:
    """Return the least approximate minimizer under ``2*error < gap``."""
    if not approximations:
        raise ValueError("empty score list")
    if error < 0 or gap <= 0:
        raise ValueError("error must be nonnegative and gap positive")
    if 2 * error >= gap:
        raise ValueError("guard is insufficient: require 2*error < gap")
    minimum = min(approximations)
    return next(i for i, score in enumerate(approximations) if score == minimum)


@dataclass(frozen=True)
class CubicBisectionState:
    lower: Fraction
    upper: Fraction
    halted: bool


def cubic_value(x: Fraction, y: Fraction) -> Fraction:
    return y * y * y + y - x


def cubic_bisection(x: Fraction, steps: int) -> TraceCertificate[CubicBisectionState]:
    """Exact rational bisection for the unique root of ``y^3+y=x``."""
    _require_nonnegative(steps, "steps")
    radius = abs(x) + 1
    init = CubicBisectionState(-radius, radius, False)

    def step(_time: int, state: CubicBisectionState) -> CubicBisectionState:
        if state.halted:
            return state
        midpoint = (state.lower + state.upper) / 2
        value = cubic_value(x, midpoint)
        if value == 0:
            return CubicBisectionState(midpoint, midpoint, True)
        if value < 0:
            return CubicBisectionState(midpoint, state.upper, False)
        return CubicBisectionState(state.lower, midpoint, False)

    def invariant(time: int, state: CubicBisectionState) -> bool:
        bracket = (
            state.lower <= state.upper
            and cubic_value(x, state.lower) <= 0
            and cubic_value(x, state.upper) >= 0
        )
        width = state.upper - state.lower
        width_bound = width * (2**time) <= 2 * radius
        halted_consistent = (not state.halted) or state.lower == state.upper
        return bracket and width_bound and halted_consistent

    return run_trace(
        init,
        step,
        steps,
        invariant,
        terminal=lambda state: invariant(steps, state),
    )


def cubic_strictly_increasing(a: Fraction, b: Fraction) -> bool:
    """Exact check of the factorized monotonicity identity for ``a < b``."""
    if not a < b:
        raise ValueError("require a < b")
    factor = a * a + a * b + b * b + 1
    lhs = (b * b * b + b) - (a * a * a + a)
    return lhs == (b - a) * factor and factor > 0 and lhs > 0


@dataclass(frozen=True)
class HeightEnumeration(Generic[X]):
    enumerate_box: Callable[[int], Iterable[X]]
    height: Callable[[X], int]
    predicate: Callable[[X], bool]
    canonical_key: Callable[[X], Hashable]

    def list_from_bound(self, bound: int) -> tuple[X, ...]:
        _require_nonnegative(bound, "bound")
        seen: set[Hashable] = set()
        result: list[X] = []
        for candidate in self.enumerate_box(bound):
            if self.height(candidate) > bound or not self.predicate(candidate):
                continue
            key = self.canonical_key(candidate)
            if key in seen:
                continue
            seen.add(key)
            result.append(candidate)
        return tuple(result)

    def bound_from_complete_list(self, points: Sequence[X]) -> int:
        if not points:
            return 0
        return max(self.height(point) for point in points)


def finite_net_upper_bound(
    evaluations: Sequence[Fraction],
    *,
    evaluation_error: Fraction,
    transport_error: Fraction,
) -> Fraction:
    """Certified upper bound from finite net values and two error budgets."""
    if not evaluations:
        raise ValueError("net must be nonempty")
    if evaluation_error < 0 or transport_error < 0:
        raise ValueError("errors must be nonnegative")
    return max(evaluations) + evaluation_error + transport_error


def least_zero(bound: int, body: Callable[[int], int]) -> int:
    """Mirror the current checked ``Search.mu`` sentinel convention.

    Return the least ``i < bound`` with ``body(i) == 0``; return ``bound`` when
    there is no zero.  The loop deliberately scans the full prefix and freezes
    after the first zero.
    """
    _require_nonnegative(bound, "bound")
    witness = 0
    for index in range(bound):
        if witness == index and body(index) != 0:
            witness += 1
    return witness


def least_zero_spec(bound: int, body: Callable[[int], int]) -> bool:
    """Finite executable check of the three checked Search invariants."""
    witness = least_zero(bound, body)
    if not 0 <= witness <= bound:
        return False
    if witness < bound and body(witness) != 0:
        return False
    return all(body(index) != 0 for index in range(witness))


@dataclass(frozen=True)
class CappedDemandEdge:
    """Provider demand induced by a consumer demand."""

    provider: str
    consumer: str
    transform: Callable[[int], int]


@dataclass(frozen=True)
class CappedClosureResult:
    vector: Mapping[str, int]
    states: tuple[Mapping[str, int], ...]
    fixed: bool
    overflow: bool
    fuel: int


@dataclass(frozen=True)
class CappedDemandSystem:
    """Finite monotone demand system, allowing dependency cycles.

    ``transform`` functions are assumed monotone; the tests exercise this
    assumption on the finite capped domain.  Saturation is reported as
    overflow rather than silently treated as raw adequacy.
    """

    nodes: tuple[str, ...]
    seed: Mapping[str, int]
    cap: Mapping[str, int]
    edges: tuple[CappedDemandEdge, ...]

    def __post_init__(self) -> None:
        if len(set(self.nodes)) != len(self.nodes):
            raise ValueError("node names must be unique")
        known = set(self.nodes)
        if set(self.seed) != known or set(self.cap) != known:
            raise ValueError("seed and cap must have exactly the node keys")
        for node in self.nodes:
            _require_nonnegative(self.seed[node], f"seed[{node}]")
            _require_nonnegative(self.cap[node], f"cap[{node}]")
            if self.seed[node] > self.cap[node]:
                raise ValueError("seed exceeds cap")
        for edge in self.edges:
            if edge.provider not in known or edge.consumer not in known:
                raise ValueError("unknown edge endpoint")

    @property
    def fuel(self) -> int:
        return 1 + sum(self.cap[n] - self.seed[n] for n in self.nodes)

    def raw_demands(self, vector: Mapping[str, int]) -> dict[str, int]:
        raw = {node: max(vector[node], self.seed[node]) for node in self.nodes}
        for edge in self.edges:
            value = edge.transform(vector[edge.consumer])
            _require_nonnegative(value, "edge demand")
            raw[edge.provider] = max(raw[edge.provider], value)
        return raw

    def update(self, vector: Mapping[str, int]) -> dict[str, int]:
        raw = self.raw_demands(vector)
        return {node: min(self.cap[node], raw[node]) for node in self.nodes}

    def overflow_at(self, vector: Mapping[str, int]) -> bool:
        raw = self.raw_demands(vector)
        return any(raw[node] > self.cap[node] for node in self.nodes)

    def rank(self, vector: Mapping[str, int]) -> int:
        return sum(vector[node] - self.seed[node] for node in self.nodes)

    def close(self) -> CappedClosureResult:
        current = dict(self.seed)
        states: list[Mapping[str, int]] = [dict(current)]
        for _ in range(self.fuel):
            current = self.update(current)
            states.append(dict(current))
        fixed = self.update(current) == current
        if not fixed:
            raise AssertionError("rank bound failed to stabilize the capped map")
        return CappedClosureResult(
            vector=dict(current),
            states=tuple(states),
            fixed=True,
            overflow=self.overflow_at(current),
            fuel=self.fuel,
        )

    def is_prefixed(self, candidate: Mapping[str, int]) -> bool:
        if set(candidate) != set(self.nodes):
            return False
        if any(
            not self.seed[n] <= candidate[n] <= self.cap[n]
            for n in self.nodes
        ):
            return False
        updated = self.update(candidate)
        return all(updated[n] <= candidate[n] for n in self.nodes)

    def is_raw_closed(self, candidate: Mapping[str, int]) -> bool:
        if not self.is_prefixed(candidate):
            return False
        raw = self.raw_demands(candidate)
        return all(raw[n] <= candidate[n] for n in self.nodes)

    def least_against(self, candidate: Mapping[str, int]) -> bool:
        if not self.is_prefixed(candidate):
            return False
        closed = self.close().vector
        return all(closed[n] <= candidate[n] for n in self.nodes)

    def monotone_on_box(self) -> bool:
        """Exhaustive monotonicity check, intended only for small test boxes."""
        ranges = [range(self.seed[n], self.cap[n] + 1) for n in self.nodes]
        vectors = [dict(zip(self.nodes, values, strict=True)) for values in product(*ranges)]
        for left in vectors:
            for right in vectors:
                if all(left[n] <= right[n] for n in self.nodes):
                    ul = self.update(left)
                    ur = self.update(right)
                    if any(ul[n] > ur[n] for n in self.nodes):
                        return False
        return True

    def brute_prefixed_points(self) -> tuple[Mapping[str, int], ...]:
        ranges = [range(self.seed[n], self.cap[n] + 1) for n in self.nodes]
        result: list[Mapping[str, int]] = []
        for values in product(*ranges):
            candidate = dict(zip(self.nodes, values, strict=True))
            if self.is_prefixed(candidate):
                result.append(candidate)
        return tuple(result)


@dataclass(frozen=True, order=True)
class ResidualBoundary:
    key: str
    formula: str
    origin: str = ""


@dataclass(frozen=True)
class ResidualNode:
    name: str
    proof_parents: tuple[str, ...] = ()
    boundaries: tuple[ResidualBoundary, ...] = ()


@dataclass(frozen=True)
class ResidualPlan:
    reachable: tuple[str, ...]
    residuals: tuple[ResidualBoundary, ...]


def normalize_residuals(
    nodes: Mapping[str, ResidualNode],
    sinks: Iterable[str],
) -> ResidualPlan:
    """Backward proof reachability and stable-key residual deduplication."""
    sink_tuple = tuple(sinks)
    unknown = [name for name in sink_tuple if name not in nodes]
    if unknown:
        raise ValueError(f"unknown sinks: {unknown!r}")
    seen: set[str] = set()
    stack = list(sink_tuple)
    while stack:
        name = stack.pop()
        if name in seen:
            continue
        seen.add(name)
        node = nodes[name]
        for parent in node.proof_parents:
            if parent not in nodes:
                raise ValueError(f"unknown proof parent {parent!r}")
            stack.append(parent)
    by_key: dict[str, ResidualBoundary] = {}
    for name in sorted(seen):
        for boundary in nodes[name].boundaries:
            existing = by_key.get(boundary.key)
            if existing is not None and existing.formula != boundary.formula:
                raise ValueError(f"residual key collision at {boundary.key!r}")
            by_key[boundary.key] = boundary
    return ResidualPlan(
        reachable=tuple(sorted(seen)),
        residuals=tuple(by_key[key] for key in sorted(by_key)),
    )
