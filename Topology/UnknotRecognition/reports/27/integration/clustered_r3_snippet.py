"""Opt-in causal-branch RIII search for ProveIt's ``fastunknot.simplify``.

Target baseline:
  repository commit 23893144e3aafd074a23cfb633222ab7e03e6d2e
  ``simplify.py`` blob 2fcaabb51eaa45cf84bdee32cd1b4e18acf2c478

The code is intentionally duck-typed against the private ``_Darts`` class.  It
has been syntax-checked and its search logic is independently tested in the
abstract prototype, but it has NOT been run against the full ProveIt checkout in
this environment.  The default repository search should remain unchanged until
its own regression and timing suites pass.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable


@dataclass
class ClusterSearchStats:
    trial_moves: int = 0
    birth_candidates: int = 0
    connected_candidates: int = 0
    duplicate_triangles: int = 0
    budget_exhaustions: int = 0


def _alive_darts(state) -> list[int]:
    return [
        4 * crossing + slot
        for crossing, alive in enumerate(state.alive)
        if alive
        for slot in range(4)
    ]


def _triangle_key(triangle) -> tuple[tuple[int, ...], tuple[int, ...]]:
    return (
        tuple(sorted(dart // 4 for dart in triangle)),
        tuple(sorted(triangle)),
    )


def _unique_triangles(state, darts: Iterable[int], stats: ClusterSearchStats):
    seen: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
    for dart in darts:
        triangle = state.triangle_at(dart)
        if triangle is None:
            continue
        key = _triangle_key(triangle)
        if key in seen:
            stats.duplicate_triangles += 1
            continue
        seen.add(key)
        yield key, triangle


def r3_footprint(state, triangle) -> frozenset[int]:
    """A conservative fixed-dart footprint for one RIII move.

    ``apply_r3`` changes pairings only among the twelve darts at the three
    crossings and their current edge partners.  The set has at most 24 darts.
    Adding the pre-move set to the accumulated support is sufficient: the move
    reconnects those same outside partners, so no new external dart appears.
    """

    local = {
        4 * (dart // 4) + slot
        for dart in triangle
        for slot in range(4)
    }
    return frozenset(local | {state.alpha[dart] for dart in local})


def _darts_meeting_footprint(state, footprint: frozenset[int]) -> list[int]:
    """Darts at crossings that can support a triangle meeting ``footprint``."""

    crossings: set[int] = set()
    for dart in footprint:
        crossing = dart // 4
        if 0 <= crossing < len(state.alive) and state.alive[crossing]:
            crossings.add(crossing)
        partner = state.alpha[dart]
        partner_crossing = partner // 4
        if 0 <= partner_crossing < len(state.alive) and state.alive[partner_crossing]:
            crossings.add(partner_crossing)
    return [4 * crossing + slot for crossing in sorted(crossings) for slot in range(4)]


def _terminal_darts(footprint: frozenset[int]) -> list[int]:
    crossings = sorted({dart // 4 for dart in footprint})
    return [4 * crossing + slot for crossing in crossings for slot in range(4)]


def _undo(state, triangle) -> None:
    inverse = state.triangle_at(triangle[0] ^ 2)
    if inverse is None or state.apply_r3(inverse) is None:
        raise ArithmeticError("failed to undo an RIII trial move")


def _search(
    state,
    depth_left: int,
    max_births: int,
    births_used: int,
    birth_phase: bool,
    last_birth_key,
    active: frozenset[int],
    undo_triangle,
    path: list,
    check_faces: bool,
    stats: ClusterSearchStats,
):
    if depth_left <= 0:
        return None
    if state.trials >= state.budget:
        stats.budget_exhaustions += 1
        return None

    # Births are globally located, pairwise footprint-disjoint moves.  They are
    # enumerated in a canonical order because they commute.  Once a connected
    # move is taken, the birth phase is over.
    if birth_phase and births_used < max_births:
        for key, triangle in _unique_triangles(state, _alive_darts(state), stats):
            if last_birth_key is not None and key <= last_birth_key:
                continue
            footprint = r3_footprint(state, triangle)
            if not active.isdisjoint(footprint):
                continue
            if undo_triangle is not None and frozenset(triangle) == undo_triangle:
                continue
            if depth_left == 1 and check_faces and not state.r3_can_help(triangle):
                continue
            if state.apply_r3(triangle) is None:
                continue
            state.trials += 1
            stats.trial_moves += 1
            stats.birth_candidates += 1
            path.append(triangle)
            new_active = active | footprint
            around = _terminal_darts(footprint)
            if any(state.move_at(dart) is not None for dart in around):
                return around
            if depth_left > 1:
                found = _search(
                    state,
                    depth_left - 1,
                    max_births,
                    births_used + 1,
                    True,
                    key,
                    new_active,
                    frozenset(dart ^ 2 for dart in triangle),
                    path,
                    check_faces,
                    stats,
                )
                if found is not None:
                    return found + around
            path.pop()
            _undo(state, triangle)
            if state.trials >= state.budget:
                stats.budget_exhaustions += 1
                return None

    if not active:
        return None

    candidate_darts = _darts_meeting_footprint(state, active)
    for _, triangle in _unique_triangles(state, candidate_darts, stats):
        footprint = r3_footprint(state, triangle)
        if active.isdisjoint(footprint):
            continue
        if undo_triangle is not None and frozenset(triangle) == undo_triangle:
            continue
        if depth_left == 1 and check_faces and not state.r3_can_help(triangle):
            continue
        if state.apply_r3(triangle) is None:
            continue
        state.trials += 1
        stats.trial_moves += 1
        stats.connected_candidates += 1
        path.append(triangle)
        new_active = active | footprint
        around = _terminal_darts(footprint)
        if any(state.move_at(dart) is not None for dart in around):
            return around
        if depth_left > 1:
            found = _search(
                state,
                depth_left - 1,
                max_births,
                births_used,
                False,
                last_birth_key,
                new_active,
                frozenset(dart ^ 2 for dart in triangle),
                path,
                check_faces,
                stats,
            )
            if found is not None:
                return found + around
        path.pop()
        _undo(state, triangle)
        if state.trials >= state.budget:
            stats.budget_exhaustions += 1
            return None
    return None


def search_clustered_unlock(
    state,
    depth: int,
    *,
    max_births: int = 1,
    check_faces: bool = True,
    path: list | None = None,
    stats: ClusterSearchStats | None = None,
):
    """Find an RIII sequence in birth-front normal form that unlocks RI/RII.

    The successful moves remain applied, matching the contract of the existing
    private ``_unlock`` function.  Failure restores the state.  ``max_births=1``
    is the accumulated-support search; larger values admit independent causal
    branches.  The caller should retain the existing global trial budget.
    """

    if type(depth) is not int or depth < 1:
        raise ValueError("depth must be a positive integer")
    if type(max_births) is not int or max_births < 1:
        raise ValueError("max_births must be a positive integer")
    if path is None:
        path = []
    if stats is None:
        stats = ClusterSearchStats()
    return _search(
        state,
        depth,
        max_births,
        0,
        True,
        None,
        frozenset(),
        None,
        path,
        check_faces,
        stats,
    )
