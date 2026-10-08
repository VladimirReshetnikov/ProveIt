"""Causal-branch search for bounded-local reversible rewrite systems.

This module is a small, dependency-free reference implementation accompanying
Report 25.  It is deliberately generic: the production ProveIt RIII adapter is
in ``integration/clustered_r3_snippet.py``.

A neutral move has a finite, stable support and is an involution.  Its guard
only reads sites in that support.  Therefore moves with disjoint supports
commute and preserve each other's legality.  A reduction is a local predicate.
The search below enumerates a normal form in which all support-disjoint
"birth" moves are placed before every support-connected move.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Iterable, Sequence


@dataclass(frozen=True, order=True)
class Move:
    """A reversible guarded bit toggle.

    ``support`` must contain all guarded and toggled sites.  Guards do not read
    toggled sites; hence applying a legal move twice returns to the original
    state and the second application is legal.
    """

    name: str
    support: frozenset[int]
    toggle: frozenset[int]
    guard: tuple[tuple[int, int], ...] = ()

    def __post_init__(self) -> None:
        if not self.toggle:
            raise ValueError("a neutral move must toggle at least one site")
        guarded = {site for site, value in self.guard}
        if any(value not in (0, 1) for _, value in self.guard):
            raise ValueError("guard values must be 0 or 1")
        if guarded & set(self.toggle):
            raise ValueError("guards may not read toggled sites")
        if not (guarded | set(self.toggle)) <= set(self.support):
            raise ValueError("support must contain all guarded and toggled sites")

    def legal(self, state: int) -> bool:
        return all(((state >> site) & 1) == value for site, value in self.guard)

    def apply(self, state: int) -> int:
        if not self.legal(state):
            raise ValueError(f"illegal move {self.name!r}")
        mask = 0
        for site in self.toggle:
            mask ^= 1 << site
        return state ^ mask


@dataclass(frozen=True, order=True)
class Reduction:
    """A local terminal predicate."""

    name: str
    support: frozenset[int]
    required: tuple[tuple[int, int], ...]

    def __post_init__(self) -> None:
        if any(value not in (0, 1) for _, value in self.required):
            raise ValueError("required values must be 0 or 1")
        if not {site for site, _ in self.required} <= set(self.support):
            raise ValueError("support must contain all inspected sites")

    def legal(self, state: int) -> bool:
        return all(((state >> site) & 1) == value for site, value in self.required)


@dataclass(frozen=True)
class BooleanLocalSystem:
    n_sites: int
    moves: tuple[Move, ...]
    reductions: tuple[Reduction, ...]

    def __post_init__(self) -> None:
        if self.n_sites < 1:
            raise ValueError("n_sites must be positive")
        universe = set(range(self.n_sites))
        for move in self.moves:
            if not set(move.support) <= universe:
                raise ValueError(f"move {move.name!r} uses an out-of-range site")
        for reduction in self.reductions:
            if not set(reduction.support) <= universe:
                raise ValueError(
                    f"reduction {reduction.name!r} uses an out-of-range site"
                )
        if len({move.name for move in self.moves}) != len(self.moves):
            raise ValueError("move names must be unique")

    def legal_moves(self, state: int) -> tuple[Move, ...]:
        return tuple(move for move in self.moves if move.legal(state))

    def legal_reductions(self, state: int) -> tuple[Reduction, ...]:
        return tuple(red for red in self.reductions if red.legal(state))

    def move_by_name(self, name: str) -> Move:
        for move in self.moves:
            if move.name == name:
                return move
        raise KeyError(name)


@dataclass(frozen=True)
class SearchResult:
    trace: tuple[str, ...] | None
    reduction: str | None
    explored_nodes: int

    @property
    def found(self) -> bool:
        return self.trace is not None


def replay(
    system: BooleanLocalSystem,
    initial_state: int,
    trace: Sequence[str],
    *,
    require_first_unlock: bool = False,
) -> tuple[int, str | None]:
    """Replay a trace and return the final state and first legal reduction.

    With ``require_first_unlock=True``, a reduction before the final move is an
    error.  This is useful for checking shortest witnesses.
    """

    state = initial_state
    if system.legal_reductions(state):
        raise ValueError("the initial state is already reducible")
    for index, name in enumerate(trace):
        move = system.move_by_name(name)
        state = move.apply(state)
        reductions = system.legal_reductions(state)
        if reductions:
            if require_first_unlock and index + 1 != len(trace):
                raise ValueError("the trace unlocks a reduction before its end")
            return state, reductions[0].name
    return state, None


def birth_number(system: BooleanLocalSystem, trace: Sequence[str]) -> int:
    """Count support components introduced chronologically by ``trace``."""

    active: set[int] = set()
    births = 0
    for name in trace:
        support = set(system.move_by_name(name).support)
        if active.isdisjoint(support):
            births += 1
        active.update(support)
    return births


def frontload_births(
    system: BooleanLocalSystem, trace: Sequence[str]
) -> tuple[str, ...]:
    """Move all birth actions to the front, preserving all other order.

    In a local system with stable supports, a birth is disjoint from every
    preceding action, so it commutes left across all of them.  Births are
    pairwise disjoint.  The returned word is therefore trace-equivalent.  A
    terminal predicate can become true earlier; callers may truncate there.
    """

    active: set[int] = set()
    births: list[str] = []
    connected: list[str] = []
    for name in trace:
        support = set(system.move_by_name(name).support)
        if active.isdisjoint(support):
            births.append(name)
        else:
            connected.append(name)
        active.update(support)
    return tuple(sorted(births)) + tuple(connected)


def truncate_at_first_reduction(
    system: BooleanLocalSystem, initial_state: int, trace: Sequence[str]
) -> tuple[str, ...]:
    state = initial_state
    for index, name in enumerate(trace):
        state = system.move_by_name(name).apply(state)
        if system.legal_reductions(state):
            return tuple(trace[: index + 1])
    return tuple(trace)


def shortest_unlock_bfs(
    system: BooleanLocalSystem, initial_state: int, max_depth: int
) -> SearchResult:
    """Unrestricted breadth-first search, used only as a finite oracle."""

    if max_depth < 0:
        raise ValueError("max_depth must be nonnegative")
    reductions = system.legal_reductions(initial_state)
    if reductions:
        return SearchResult((), reductions[0].name, 1)

    queue: deque[tuple[int, tuple[str, ...]]] = deque([(initial_state, ())])
    best_depth = {initial_state: 0}
    explored = 0
    while queue:
        state, trace = queue.popleft()
        explored += 1
        if len(trace) == max_depth:
            continue
        for move in system.legal_moves(state):
            new_state = move.apply(state)
            new_trace = trace + (move.name,)
            reductions = system.legal_reductions(new_state)
            if reductions:
                return SearchResult(new_trace, reductions[0].name, explored)
            new_depth = len(new_trace)
            if best_depth.get(new_state, max_depth + 1) <= new_depth:
                continue
            best_depth[new_state] = new_depth
            queue.append((new_state, new_trace))
    return SearchResult(None, None, explored)


def _birth_front_dfs(
    system: BooleanLocalSystem,
    state: int,
    depth_left: int,
    max_births: int,
    active: frozenset[int],
    births_used: int,
    birth_phase: bool,
    last_birth_name: str,
    trace: tuple[str, ...],
    explored: list[int],
    memo: set[tuple[int, int, int, frozenset[int], bool, str]],
) -> tuple[tuple[str, ...], str] | None:
    explored[0] += 1
    key = (
        state,
        depth_left,
        births_used,
        active,
        birth_phase,
        last_birth_name,
    )
    if key in memo:
        return None
    memo.add(key)
    if depth_left == 0:
        return None

    legal = system.legal_moves(state)

    # Births are pairwise disjoint, commute, and are enumerated canonically by
    # name.  Once a connected action is taken the birth phase is over.
    if birth_phase and births_used < max_births:
        for move in legal:
            if move.name <= last_birth_name:
                continue
            if not active.isdisjoint(move.support):
                continue
            new_state = move.apply(state)
            new_trace = trace + (move.name,)
            reductions = system.legal_reductions(new_state)
            if reductions:
                return new_trace, reductions[0].name
            found = _birth_front_dfs(
                system,
                new_state,
                depth_left - 1,
                max_births,
                active | move.support,
                births_used + 1,
                True,
                move.name,
                new_trace,
                explored,
                memo,
            )
            if found is not None:
                return found

    # The connected phase may start after any positive number of births.  Every
    # later support must intersect the accumulated support.
    if active:
        for move in legal:
            if active.isdisjoint(move.support):
                continue
            new_state = move.apply(state)
            new_trace = trace + (move.name,)
            reductions = system.legal_reductions(new_state)
            if reductions:
                return new_trace, reductions[0].name
            found = _birth_front_dfs(
                system,
                new_state,
                depth_left - 1,
                max_births,
                active | move.support,
                births_used,
                False,
                last_birth_name,
                new_trace,
                explored,
                memo,
            )
            if found is not None:
                return found
    return None


def birth_front_unlock(
    system: BooleanLocalSystem,
    initial_state: int,
    max_depth: int,
    max_births: int,
) -> SearchResult:
    """Search the birth-front normal form up to the supplied parameters.

    The routine is complete for first-unlocking traces of length at most
    ``max_depth`` and birth number at most ``max_births`` under the local
    commutation hypotheses encoded by :class:`Move`.  The search does not
    prune a branch merely because its physical state repeats: the accumulated
    footprint is part of the parameterized search state and can change which
    later moves count as births.
    """

    if max_depth < 0:
        raise ValueError("max_depth must be nonnegative")
    if max_births < 1:
        raise ValueError("max_births must be positive")
    reductions = system.legal_reductions(initial_state)
    if reductions:
        return SearchResult((), reductions[0].name, 1)

    explored = [0]
    # Iterative deepening gives a shortest trace within the normal-form search.
    for depth in range(1, max_depth + 1):
        memo: set[tuple[int, int, int, frozenset[int], bool, str]] = set()
        found = _birth_front_dfs(
            system,
            initial_state,
            depth,
            max_births,
            frozenset(),
            0,
            True,
            "",
            (),
            explored,
            memo,
        )
        if found is not None:
            trace, reduction = found
            return SearchResult(trace, reduction, explored[0])
    return SearchResult(None, None, explored[0])


def _last_touch_dfs(
    system: BooleanLocalSystem,
    state: int,
    depth_left: int,
    last_support: frozenset[int] | None,
    trace: tuple[str, ...],
    explored: list[int],
) -> tuple[tuple[str, ...], str] | None:
    explored[0] += 1
    if depth_left == 0:
        return None
    for move in system.legal_moves(state):
        if last_support is not None and last_support.isdisjoint(move.support):
            continue
        new_state = move.apply(state)
        new_trace = trace + (move.name,)
        reductions = system.legal_reductions(new_state)
        if reductions:
            return new_trace, reductions[0].name
        found = _last_touch_dfs(
            system,
            new_state,
            depth_left - 1,
            move.support,
            new_trace,
            explored,
        )
        if found is not None:
            return found
    return None


def last_touch_unlock(
    system: BooleanLocalSystem, initial_state: int, max_depth: int
) -> SearchResult:
    """Reference model of the repository's immediate-neighbour chain search."""

    explored = [0]
    for depth in range(1, max_depth + 1):
        found = _last_touch_dfs(
            system,
            initial_state,
            depth,
            None,
            (),
            explored,
        )
        if found is not None:
            trace, reduction = found
            return SearchResult(trace, reduction, explored[0])
    return SearchResult(None, None, explored[0])


def dependency_graph(
    system: BooleanLocalSystem,
    trace: Sequence[str],
    reduction_name: str,
) -> dict[str, set[str]]:
    """Return the support-overlap graph of action instances and the terminal.

    Vertices are ``m0``, ..., ``m{k-1}``, and ``R``.  This helper is for
    diagnostics; the manuscript proves that a shortest first-unlocking trace
    has a connected graph whenever disjoint actions strongly commute.
    """

    reduction = next(red for red in system.reductions if red.name == reduction_name)
    supports = [system.move_by_name(name).support for name in trace]
    labels = [f"m{i}" for i in range(len(trace))] + ["R"]
    all_supports = supports + [reduction.support]
    graph = {label: set() for label in labels}
    for i, left in enumerate(all_supports):
        for j in range(i + 1, len(all_supports)):
            if left.isdisjoint(all_supports[j]):
                continue
            graph[labels[i]].add(labels[j])
            graph[labels[j]].add(labels[i])
    return graph


def graph_connected(graph: dict[str, set[str]]) -> bool:
    if not graph:
        return True
    start = next(iter(graph))
    stack = [start]
    seen = {start}
    while stack:
        vertex = stack.pop()
        for neighbour in graph[vertex]:
            if neighbour not in seen:
                seen.add(neighbour)
                stack.append(neighbour)
    return len(seen) == len(graph)



def support_history_example() -> tuple[BooleanLocalSystem, int]:
    """A one-birth witness whose accumulated support survives a state repeat.

    The unrestricted shortest witness ``D,E`` has two births.  A one-birth
    normal-form witness is ``B,C,D,E``: after ``B,C`` the physical bit state is
    again the initial state, but the accumulated support now connects sites 0
    and 2.  Pruning solely on repeated physical states would therefore destroy
    completeness under a birth bound.
    """

    moves = (
        Move("B", frozenset({0, 1}), frozenset({1})),
        Move("C", frozenset({1, 2}), frozenset({1})),
        Move("D", frozenset({0}), frozenset({0})),
        Move("E", frozenset({2}), frozenset({2})),
    )
    reductions = (
        Reduction("R", frozenset({0, 1, 2}), ((0, 1), (1, 0), (2, 1))),
    )
    return BooleanLocalSystem(3, moves, reductions), 0

def branching_example() -> tuple[BooleanLocalSystem, int]:
    """A shortest trace with two independent births joined by a later move."""

    moves = (
        Move("A", frozenset({0}), frozenset({0})),
        Move("B", frozenset({2}), frozenset({2})),
        Move(
            "C",
            frozenset({0, 1, 2}),
            frozenset({1}),
            ((0, 1), (2, 1)),
        ),
    )
    reductions = (Reduction("R", frozenset({1}), ((1, 1),)),)
    return BooleanLocalSystem(3, moves, reductions), 0


def accumulated_strict_example() -> tuple[BooleanLocalSystem, int]:
    """One birth suffices, but no consecutive-support chain can unlock.

    A enables two commuting leaves B and C.  Their supports are disjoint, so a
    search that insists that each move touch only its immediate predecessor
    cannot take both.  An accumulated-support search can.
    """

    moves = (
        Move("A", frozenset({0, 1}), frozenset({0, 1})),
        Move("B", frozenset({0, 2}), frozenset({2}), ((0, 1),)),
        Move("C", frozenset({1, 3}), frozenset({3}), ((1, 1),)),
    )
    reductions = (Reduction("R", frozenset({2, 3}), ((2, 1), (3, 1))),)
    return BooleanLocalSystem(4, moves, reductions), 0


__all__ = [
    "BooleanLocalSystem",
    "Move",
    "Reduction",
    "SearchResult",
    "accumulated_strict_example",
    "birth_front_unlock",
    "birth_number",
    "branching_example",
    "dependency_graph",
    "frontload_births",
    "graph_connected",
    "last_touch_unlock",
    "replay",
    "shortest_unlock_bfs",
    "truncate_at_first_reduction",
]
