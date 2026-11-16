"""Exact finite reference implementation for the PFIG report.

This module is deliberately small and transparent.  It validates the finite
algorithms used in the human proofs: Boolean folds, least bounded search,
reverse precision demand, trace checking, backward viability, canonical
finite-horizon observations, guarded branch stabilization, and height/list
conversion.  It is *not* an iPRA proof checker; object-language correctness is
specified separately in the Lean blueprint.
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
    MutableMapping,
    Sequence,
    TypeVar,
)

T = TypeVar("T", bound=Hashable)
S = TypeVar("S")
P = TypeVar("P")


def bounded_all(bound: int, predicate: Callable[[int], bool]) -> bool:
    """Finite universal fold over ``0 <= i < bound``."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    acc = True
    for i in range(bound):
        acc = acc and bool(predicate(i))
    return acc


def bounded_any(bound: int, predicate: Callable[[int], bool]) -> bool:
    """Finite existential fold over ``0 <= i < bound``."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    acc = False
    for i in range(bound):
        acc = acc or bool(predicate(i))
    return acc


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
    """Return the least witness below ``bound`` or a specified default.

    The loop follows the report's ``(found, witness)`` state rather than using
    Python's ``next``; this mirrors the primitive-recursive implementation.
    """
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    found = False
    witness = default
    for i in range(bound):
        hit = bool(predicate(i))
        if (not found) and hit:
            found = True
            witness = i
    return SearchResult(found=found, witness=witness)


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
    """Execute a bounded recurrence and check its invariant at every state."""
    if fuel < 0:
        raise ValueError("fuel must be nonnegative")
    states: list[S] = [init]
    invariant_holds = bool(invariant(0, init))
    state = init
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
    """An edge from a provider to a consumer.

    ``transform`` maps the consumer's request to the provider's required
    request.  Requests are scalar naturals in the reference implementation.
    """

    provider: str
    consumer: str
    transform: Callable[[int, P], int]


@dataclass(frozen=True)
class DemandGraph(Generic[P]):
    """A fixed acyclic graph in provider-before-consumer topological order."""

    nodes: tuple[str, ...]
    edges: tuple[DemandEdge[P], ...]

    def __post_init__(self) -> None:
        if len(set(self.nodes)) != len(self.nodes):
            raise ValueError("node names must be unique")
        index = {name: i for i, name in enumerate(self.nodes)}
        for edge in self.edges:
            if edge.provider not in index or edge.consumer not in index:
                raise ValueError(f"unknown endpoint in edge {edge}")
            if index[edge.provider] >= index[edge.consumer]:
                raise ValueError(
                    "nodes must be topological: provider must precede consumer"
                )

    def reverse_demands(
        self,
        terminal_requests: Mapping[str, int],
        params: P,
    ) -> dict[str, int]:
        """Compute the least request vector for the supplied edge equations."""
        request: dict[str, int] = {name: 0 for name in self.nodes}
        for name, value in terminal_requests.items():
            if name not in request:
                raise ValueError(f"unknown terminal node {name!r}")
            if value < 0:
                raise ValueError("requests must be nonnegative")
            request[name] = max(request[name], value)

        outgoing: dict[str, list[DemandEdge[P]]] = {name: [] for name in self.nodes}
        for edge in self.edges:
            outgoing[edge.provider].append(edge)

        for provider in reversed(self.nodes):
            needed = request[provider]
            for edge in outgoing[provider]:
                transformed = edge.transform(request[edge.consumer], params)
                if transformed < 0:
                    raise ValueError("demand transform returned a negative request")
                needed = max(needed, transformed)
            request[provider] = needed
        return request

    def satisfies(
        self,
        requests: Mapping[str, int],
        terminal_requests: Mapping[str, int],
        params: P,
    ) -> bool:
        """Check terminal and edge demand inequalities."""
        if any(name not in requests for name in self.nodes):
            return False
        for name, value in terminal_requests.items():
            if requests.get(name, -1) < value:
                return False
        return all(
            requests[e.provider] >= e.transform(requests[e.consumer], params)
            for e in self.edges
        )


@dataclass(frozen=True)
class FiniteRelationTower(Generic[T]):
    """Finite candidate levels and compatibility edges between them."""

    levels: tuple[tuple[T, ...], ...]
    edge: Callable[[int, T, T], bool]

    def __post_init__(self) -> None:
        if not self.levels:
            raise ValueError("tower must have at least one level")
        for level in self.levels:
            if len(set(level)) != len(level):
                raise ValueError("candidates within a level must be unique")

    def _check_horizon(self, horizon: int) -> None:
        if not 0 <= horizon < len(self.levels):
            raise ValueError("horizon is outside the tower")

    def viable_sets(self, horizon: int) -> tuple[frozenset[T], ...]:
        """Backward viability table for levels ``0..horizon``."""
        self._check_horizon(horizon)
        viable: list[set[T]] = [set() for _ in range(horizon + 1)]
        viable[horizon].update(self.levels[horizon])
        for level in range(horizon - 1, -1, -1):
            next_viable = viable[level + 1]
            for candidate in self.levels[level]:
                if any(
                    self.edge(level, candidate, nxt) for nxt in next_viable
                ):
                    viable[level].add(candidate)
        return tuple(frozenset(row) for row in viable)

    def brute_paths(
        self,
        start_level: int,
        horizon: int,
        start: T | None = None,
    ) -> tuple[tuple[T, ...], ...]:
        """Enumerate all compatible paths; intended only as a test oracle."""
        self._check_horizon(horizon)
        if not 0 <= start_level <= horizon:
            raise ValueError("invalid start level")
        rows: Sequence[Sequence[T]] = self.levels[start_level : horizon + 1]
        paths: list[tuple[T, ...]] = []
        for candidate_path in product(*rows):
            if start is not None and candidate_path[0] != start:
                continue
            if all(
                self.edge(start_level + i, candidate_path[i], candidate_path[i + 1])
                for i in range(len(candidate_path) - 1)
            ):
                paths.append(tuple(candidate_path))
        return tuple(paths)

    def viability_matches_paths(self, horizon: int) -> bool:
        """Check the viability/path equivalence for every candidate."""
        viable = self.viable_sets(horizon)
        for level in range(horizon + 1):
            for candidate in self.levels[level]:
                has_path = bool(self.brute_paths(level, horizon, candidate))
                if (candidate in viable[level]) != has_path:
                    return False
        return True

    def least_viable_path(
        self,
        horizon: int,
        *,
        start_level: int = 0,
        key: Callable[[T], object] | None = None,
    ) -> tuple[T, ...]:
        """Return the lexicographically least path selected from viability."""
        self._check_horizon(horizon)
        if not 0 <= start_level <= horizon:
            raise ValueError("invalid start level")
        order = key or (lambda x: x)
        viable = self.viable_sets(horizon)
        starts = sorted(viable[start_level], key=order)
        if not starts:
            raise ValueError("no viable start candidate")
        path: list[T] = [starts[0]]
        for level in range(start_level, horizon):
            successors = sorted(
                (
                    b
                    for b in viable[level + 1]
                    if self.edge(level, path[-1], b)
                ),
                key=order,
            )
            if not successors:
                raise AssertionError("viability recurrence promised a successor")
            path.append(successors[0])
        return tuple(path)

    def path_is_valid(self, start_level: int, path: Sequence[T]) -> bool:
        if not path:
            return False
        if start_level < 0 or start_level + len(path) > len(self.levels):
            return False
        for offset, candidate in enumerate(path):
            if candidate not in self.levels[start_level + offset]:
                return False
        return all(
            self.edge(start_level + i, path[i], path[i + 1])
            for i in range(len(path) - 1)
        )

    def canonical_candidate(
        self,
        level: int,
        horizon: int,
        *,
        key: Callable[[T], object] | None = None,
    ) -> tuple[T, T | None]:
        """Choose a viable candidate, with a certified predecessor if possible.

        At level zero the predecessor is ``None``.  At a positive level we
        choose the lexicographically least pair ``(predecessor, candidate)``
        lying on a path to the horizon, then return the candidate and its
        predecessor.  This is the finite-pair convention used in the report's
        adjacent-coherence proof.
        """
        self._check_horizon(horizon)
        if not 0 <= level <= horizon:
            raise ValueError("invalid level")
        order = key or (lambda x: x)
        viable = self.viable_sets(horizon)
        if level == 0:
            choices = sorted(viable[0], key=order)
            if not choices:
                raise ValueError("no viable candidate")
            return choices[0], None

        pairs = [
            (a, b)
            for a in viable[level - 1]
            for b in viable[level]
            if self.edge(level - 1, a, b)
        ]
        if not pairs:
            raise ValueError("no viable predecessor/candidate pair")
        pairs.sort(key=lambda pair: (order(pair[0]), order(pair[1])))
        predecessor, candidate = pairs[0]
        return candidate, predecessor


def canonical_observations(
    tower: FiniteRelationTower[T],
    max_level: int,
    horizon: Callable[[int], int],
    observation: Callable[[int, T], Fraction],
    *,
    key: Callable[[T], object] | None = None,
) -> tuple[tuple[Fraction, T, T | None], ...]:
    """Compute finite-horizon canonical observations through ``max_level``."""
    if max_level < 0:
        raise ValueError("max_level must be nonnegative")
    result: list[tuple[Fraction, T, T | None]] = []
    previous_horizon = -1
    for level in range(max_level + 1):
        h = horizon(level)
        if h < level or h >= len(tower.levels):
            raise ValueError("horizon(level) must lie within the tower")
        if h < previous_horizon:
            raise ValueError("horizon must be nondecreasing")
        candidate, predecessor = tower.canonical_candidate(level, h, key=key)
        result.append((observation(level, candidate), candidate, predecessor))
        previous_horizon = h
    return tuple(result)


def check_adjacent_coherence(
    canonical: Sequence[tuple[Fraction, T, T | None]],
    observation: Callable[[int, T], Fraction],
    diameter: Callable[[int], Fraction],
    motion: Callable[[int], Fraction],
) -> bool:
    """Check the report's adjacent bound using each selected predecessor."""
    for level in range(len(canonical) - 1):
        x = canonical[level][0]
        y, _, predecessor = canonical[level + 1]
        if predecessor is None:
            return False
        predecessor_value = observation(level, predecessor)
        if abs(x - predecessor_value) > diameter(level):
            return False
        if abs(predecessor_value - y) > motion(level):
            return False
        if abs(x - y) > diameter(level) + motion(level):
            return False
    return True


def tail_budget(
    diameter: Callable[[int], Fraction],
    motion: Callable[[int], Fraction],
    start: int,
    stop: int,
) -> Fraction:
    """Finite motion budget from ``start`` through ``stop-1``."""
    if not 0 <= start <= stop:
        raise ValueError("invalid interval")
    return sum((diameter(i) + motion(i) for i in range(start, stop)), Fraction(0))


def stable_observer(
    certificates: Sequence[T],
    valid: Callable[[T], bool],
    observe: Callable[[T], S],
) -> S:
    """Return a witness-independent observation after checking stability.

    This executable helper checks, rather than proves, that every valid
    certificate has the same observation.  The object theorem uses local
    stability and existential elimination instead.
    """
    valid_certificates = [c for c in certificates if valid(c)]
    if not valid_certificates:
        raise ValueError("no valid certificate")
    observations = [observe(c) for c in valid_certificates]
    first = observations[0]
    if any(value != first for value in observations[1:]):
        raise ValueError("observer is not stable on valid certificates")
    return first


def guarded_argmin(
    approximate_scores: Sequence[Fraction],
    error: Fraction,
    gap: Fraction,
) -> int:
    """Select the least approximate minimizer under ``2*error < gap``."""
    if not approximate_scores:
        raise ValueError("at least one score is required")
    if error < 0 or gap <= 0:
        raise ValueError("error must be nonnegative and gap positive")
    if 2 * error >= gap:
        raise ValueError("insufficient separation: require 2*error < gap")
    return min(range(len(approximate_scores)), key=lambda i: (approximate_scores[i], i))


@dataclass(frozen=True)
class HeightEnumeration(Generic[T]):
    """Finite height-box interface."""

    enumerate_box: Callable[[int], Iterable[T]]
    height: Callable[[T], int]
    predicate: Callable[[T], bool]
    canonical_key: Callable[[T], Hashable]

    def list_from_bound(self, bound: int) -> tuple[T, ...]:
        if bound < 0:
            raise ValueError("bound must be nonnegative")
        chosen: MutableMapping[Hashable, T] = {}
        for item in self.enumerate_box(bound):
            if self.height(item) > bound:
                raise ValueError("enumerate_box returned an item above the bound")
            if self.predicate(item):
                key = self.canonical_key(item)
                chosen.setdefault(key, item)
        return tuple(chosen[key] for key in sorted(chosen, key=repr))

    def bound_from_complete_list(self, items: Sequence[T]) -> int:
        if not items:
            return 0
        if any(not self.predicate(item) for item in items):
            raise ValueError("list contains an item not satisfying the predicate")
        return max(self.height(item) for item in items)


def symmetric_quadratic_observable(ordered_roots: Sequence[Fraction]) -> tuple[Fraction, Fraction]:
    """Stable sum/product observable for a two-root presentation."""
    if len(ordered_roots) != 2:
        raise ValueError("exactly two roots are required")
    a, b = ordered_roots
    return a + b, a * b
