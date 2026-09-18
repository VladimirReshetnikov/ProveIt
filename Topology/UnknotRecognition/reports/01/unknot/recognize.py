"""Complete monotone grid search and separately replayable certificates.

Completeness uses Dynnikov's monotonic simplification theorem. The search is
finite but exponential in grid size. Resource limits return UNKNOWN, not KNOTTED.
"""
from __future__ import annotations

from collections import deque
from time import monotonic
from typing import Any

from .determinant import determinant
from .grid import DiagramError, Grid, Move, successors

FORMAT = "unknot-grid-certificate-v1"


def recognize(grid: Grid, *, max_states: int | None = None,
              timeout: float | None = None, use_determinant: bool = True,
              include_certificate: bool = True) -> dict[str, Any]:
    """Recognize a knot. No limits by default; timeout is a soft wall-time limit.

    max_states caps retained search states, not their total byte size. Timeout is
    checked between operations; a determinant or successor computation is not
    preempted. A configured limit can prevent a decision, but not falsify one.
    """
    if grid.components() != 1:
        raise DiagramError("unknot recognition requires exactly one component")
    if max_states is not None and (type(max_states) is not int or max_states < 1):
        raise ValueError("max_states must be a positive integer")
    if timeout is not None and (not isinstance(timeout, (int, float))
                                or isinstance(timeout, bool) or not 0 < timeout < float('inf')):
        raise ValueError("timeout must be positive and finite")
    start = monotonic()
    root = grid.canonical()
    parent: dict[Grid, tuple[Grid, Move] | None] = {root: None}
    expanded = 0

    def result(verdict: str, method: str, certificate: dict[str, Any] | None = None,
               **extra: Any) -> dict[str, Any]:
        data: dict[str, Any] = {
            "verdict": verdict, "method": method,
            "input_grid_size": grid.size, "input_crossings": grid.crossing_count(),
            "states_seen": len(parent), "states_expanded": expanded,
            "seconds": monotonic() - start,
            "quasipolynomial_bound_established": False,
        }
        data.update(extra)
        if include_certificate and certificate is not None:
            data["certificate"] = {"format": FORMAT, "input": grid.to_json(), **certificate}
        return data

    if use_determinant:
        value = determinant(grid)
        if value != 1:
            return result("KNOTTED", "determinant", {"kind": "determinant", "value": value},
                          determinant=value)
    queue = deque([root])
    while queue:
        if timeout is not None and monotonic() - start >= timeout:
            return result("UNKNOWN", "time_limit", frontier_size=len(queue))
        current = queue.popleft()
        if current.size == 2:
            path = []
            at = current
            while parent[at] is not None:
                previous, move = parent[at]  # type: ignore[misc]
                path.append(move.to_json())
                at = previous
            path.reverse()
            return result("UNKNOT", "monotone_path", {"kind": "path", "moves": path},
                          moves=len(path))
        expanded += 1
        for child, move in successors(current):
            if child in parent:
                continue
            if max_states is not None and len(parent) >= max_states:
                return result("UNKNOWN", "state_limit", frontier_size=len(queue) + 1)
            parent[child] = (current, move)
            if child.size < current.size:
                queue.appendleft(child)
            else:
                queue.append(child)
    # Exhaustion is conclusive only because EVERY non-increasing move was tried.
    closed = ({"kind": "closed_set",
               "states": [g.to_json() for g in sorted(parent, key=lambda g: (g.size, g.rows))]}
              if include_certificate else None)
    return result("KNOTTED", "closed_monotone_state_space", closed)


def _canonical_reference(grid: Grid) -> Grid:
    """Deliberately simple verifier implementation, independent of Booth."""
    n = grid.size
    best = min(
        tuple(tuple(sorted((c + dc) % n for c in grid.rows[(r + dr) % n]))
              for r in range(n))
        for dr in range(n) for dc in range(n)
    )
    return Grid(best)


def _verification_children(grid: Grid):
    """Enumerate all candidates, without trusting the search move generator."""
    candidates = [Move(kind, i) for kind in ("row_exchange", "column_exchange")
                  for i in range(grid.size)]
    candidates.extend(Move("destabilize", r, c)
                      for r in range(grid.size) for c in range(grid.size))
    for move in candidates:
        try:
            child = move.apply(grid)
        except DiagramError:
            continue
        yield _canonical_reference(child)


def verify_certificate(certificate: Any, expected_input: Grid | None = None) -> dict[str, Any]:
    """Verify a certificate without calling recognize or trusting its verdict.

    The verifier shares the elementary move and exact arithmetic implementation,
    but independently enumerates moves and canonicalizes cyclic shifts. This is not formal verification or an independent kernel.
    Bind expected_input when checking a certificate against a particular diagram.
    """
    if not isinstance(certificate, dict) or certificate.get("format") != FORMAT:
        raise DiagramError("unrecognized certificate format")
    grid = Grid.from_json(certificate.get("input"))
    if expected_input is not None and grid != expected_input:
        raise DiagramError("certificate is for a different input diagram")
    if grid.components() != 1:
        raise DiagramError("certificate input must be a knot")
    root = _canonical_reference(grid)
    kind = certificate.get("kind")
    if kind == "determinant":
        claimed = certificate.get("value")
        if type(claimed) is not int or claimed == 1 or claimed != determinant(grid):
            raise DiagramError("invalid determinant obstruction")
        return {"valid": True, "verdict": "KNOTTED", "kind": kind}
    if kind == "path":
        path = certificate.get("moves")
        if not isinstance(path, list):
            raise DiagramError("path moves must be an array")
        current = root
        for value in path:
            current = _canonical_reference(Move.from_json(value).apply(current))
        if current.size != 2:
            raise DiagramError("path does not end at the two-by-two unknot")
        return {"valid": True, "verdict": "UNKNOT", "kind": kind, "moves": len(path)}
    if kind == "closed_set":
        values = certificate.get("states")
        if not isinstance(values, list) or not values:
            raise DiagramError("closed set must be a nonempty array")
        states = {Grid.from_json(value) for value in values}
        if len(states) != len(values) or root not in states:
            raise DiagramError("duplicate states or missing initial state")
        for state in states:
            if state != _canonical_reference(state) or not 2 < state.size <= root.size:
                raise DiagramError("closed set contains noncanonical or inadmissible state")
            if state.components() != 1:
                raise DiagramError("closed set contains a non-knot")
            for child in _verification_children(state):
                if child not in states:
                    raise DiagramError("claimed state set is not closed under legal moves")
        return {"valid": True, "verdict": "KNOTTED", "kind": kind, "states": len(states)}
    raise DiagramError("unknown certificate kind")
