#!/usr/bin/env python3
"""Exact-case formulas for intrinsic distances on a cuboid surface.

The mathematical formulas use sorted edge lengths A <= B <= C.  The public
functions accept edges in any order and, for the fixed-vertex problem, return
the maximizing point in the original coordinates.

Only the interior diameter case requires a numerical root; it is the unique
root of a strictly increasing scalar function, so bisection is certified by
the theorem proved in the accompanying paper.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import argparse
import json
import math
from typing import Iterable, Sequence


_EPS = 1.0e-12


@dataclass(frozen=True)
class FixedVertexResult:
    sorted_edges: tuple[float, float, float]
    sorting_permutation: tuple[int, int, int]
    original_vertex: tuple[float, float, float]
    maximizing_point: tuple[float, float, float]
    maximizing_point_sorted_local: tuple[float, float, float]
    distance: float
    case: str
    K: float
    delta: float


@dataclass(frozen=True)
class DiameterResult:
    sorted_edges: tuple[float, float, float]
    sorting_permutation: tuple[int, int, int]
    endpoint_P: tuple[float, float, float]
    endpoint_Q: tuple[float, float, float]
    distance: float
    case: str
    ME_left: float
    ME_right: float
    Q_discriminant: float
    residual: float


def _validate_edges(edges: Iterable[float]) -> tuple[float, float, float]:
    values = tuple(float(v) for v in edges)
    if len(values) != 3:
        raise ValueError("Exactly three edge lengths are required.")
    if not all(math.isfinite(v) and v > 0.0 for v in values):
        raise ValueError("All edge lengths must be finite and strictly positive.")
    return values


def _sort_edges(edges: Sequence[float]) -> tuple[tuple[float, float, float], tuple[int, int, int]]:
    permutation = tuple(sorted(range(3), key=lambda i: (edges[i], i)))
    sorted_edges = tuple(edges[i] for i in permutation)
    return sorted_edges, permutation  # type: ignore[return-value]


def _validate_vertex(edges: Sequence[float], vertex: Sequence[float] | None) -> tuple[float, float, float]:
    if vertex is None:
        return (0.0, 0.0, 0.0)
    values = tuple(float(v) for v in vertex)
    if len(values) != 3:
        raise ValueError("A vertex must have three coordinates.")
    normalized: list[float] = []
    for i, (v, side) in enumerate(zip(values, edges)):
        scale = max(1.0, side)
        if abs(v) <= _EPS * scale:
            normalized.append(0.0)
        elif abs(v - side) <= _EPS * scale:
            normalized.append(side)
        else:
            raise ValueError(
                f"Coordinate {i}={v} is not a cuboid vertex coordinate (0 or {side})."
            )
    return tuple(normalized)  # type: ignore[return-value]


def _sorted_local_to_original(
    sorted_local: Sequence[float],
    edges: Sequence[float],
    permutation: Sequence[int],
    vertex: Sequence[float],
) -> tuple[float, float, float]:
    result = [0.0, 0.0, 0.0]
    for sorted_axis, original_axis in enumerate(permutation):
        t = float(sorted_local[sorted_axis])
        side = edges[original_axis]
        result[original_axis] = t if vertex[original_axis] == 0.0 else side - t
    return tuple(result)  # type: ignore[return-value]


def fixed_vertex_farthest(
    edges: Iterable[float], vertex: Sequence[float] | None = None
) -> FixedVertexResult:
    """Return one farthest surface point from a selected cuboid vertex."""

    original_edges = _validate_edges(edges)
    original_vertex = _validate_vertex(original_edges, vertex)
    (A, B, C), permutation = _sort_edges(original_edges)

    L0_sq = (A + B) ** 2 + C**2
    K = 2.0 * C**2 - 2.0 * B * C - A * C - A * B

    if K <= 0.0:
        local = (A, B, C)
        distance = math.sqrt(L0_sq)
        delta = 0.0
        case = "opposite vertex"
    else:
        delta = A * (C - B) / (2.0 * C)
        local = (A - delta, B - delta, C)
        R_sq = ((B**2 + C**2) * (A**2 + 2.0 * A * C + 2.0 * C**2)) / (
            2.0 * C**2
        )
        distance = math.sqrt(R_sq)
        case = "interior point of the face opposite the longest edge"

    point = _sorted_local_to_original(local, original_edges, permutation, original_vertex)
    return FixedVertexResult(
        sorted_edges=(A, B, C),
        sorting_permutation=permutation,
        original_vertex=original_vertex,
        maximizing_point=point,
        maximizing_point_sorted_local=local,
        distance=distance,
        case=case,
        K=K,
        delta=delta,
    )


def _diameter_root(A: float, B: float, C: float) -> tuple[float, float]:
    L0 = math.hypot(A + B, C)
    lower = max(B + C, L0)

    def radical(x: float) -> float:
        # max(0,.) only protects against tiny negative roundoff at the endpoint.
        return math.sqrt(max(0.0, x))

    def f(ell: float) -> float:
        return (
            radical(ell**2 - (A + C) ** 2)
            + radical(ell**2 - (B + C) ** 2)
            + radical(2.0 * ell**2 - (A + B + C) ** 2)
            - C
        )

    f_lower = f(lower)
    if f_lower > 1.0e-10 * max(1.0, C):
        raise ArithmeticError(
            "The theorem's root bracket failed numerically; check the case conditions."
        )
    if abs(f_lower) <= 1.0e-15 * max(1.0, C):
        return lower, f_lower

    upper = max(lower + max(A, B, C), 1.25 * lower)
    while f(upper) < 0.0:
        upper *= 2.0
        if not math.isfinite(upper):
            raise ArithmeticError("Could not bracket the unique diameter root.")

    for _ in range(180):
        middle = (lower + upper) / 2.0
        if f(middle) < 0.0:
            lower = middle
        else:
            upper = middle
    ell = (lower + upper) / 2.0
    return ell, f(ell)


def intrinsic_diameter(edges: Iterable[float]) -> DiameterResult:
    """Return one diametral pair and the intrinsic diameter."""

    original_edges = _validate_edges(edges)
    (A, B, C), permutation = _sort_edges(original_edges)
    L0 = math.hypot(A + B, C)

    alpha = math.sqrt(max(0.0, A**2 + 2.0 * A * B - 2.0 * B * C))
    beta = math.sqrt(max(0.0, B**2 + 2.0 * A * B - 2.0 * A * C))
    me_left = alpha + beta
    me_right = 2.0 * C - A - B
    q_disc = A**2 * B**2 - C**2 * (B - A) * (A + B + 2.0 * C)

    if me_left + _EPS * max(1.0, me_right) >= me_right:
        P_sorted = (0.0, 0.0, 0.0)
        Q_sorted = (A, B, C)
        distance = L0
        residual = 0.0
        case = "opposite vertices (ME region)"
    elif q_disc <= 0.0:
        H = math.sqrt((B + C) ** 2 - 2.0 * A * (C - B) - A**2)
        tau = (B + C - H) / 2.0
        P_sorted = (A / 2.0, tau, 0.0)
        Q_sorted = (A / 2.0, B - tau, C)
        D_sq = B**2 + 3.0 * C**2 + 2.0 * B * (A + C) - 2.0 * C * H
        distance = math.sqrt(D_sq)
        residual = 0.0
        case = "boundary balancing pair"
    else:
        distance, residual = _diameter_root(A, B, C)
        u = math.sqrt(max(0.0, distance**2 - (B + C) ** 2))
        v = math.sqrt(max(0.0, distance**2 - (A + C) ** 2))
        P_sorted = ((A - u) / 2.0, (B - v) / 2.0, 0.0)
        Q_sorted = ((A + u) / 2.0, (B + v) / 2.0, C)
        case = "interior triple-balancing pair"

    # For free endpoints, a simple axis permutation (without reflection) maps
    # sorted coordinates back to the original box.
    P = [0.0, 0.0, 0.0]
    Qp = [0.0, 0.0, 0.0]
    for j, i in enumerate(permutation):
        P[i] = P_sorted[j]
        Qp[i] = Q_sorted[j]

    return DiameterResult(
        sorted_edges=(A, B, C),
        sorting_permutation=permutation,
        endpoint_P=tuple(P),
        endpoint_Q=tuple(Qp),
        distance=distance,
        case=case,
        ME_left=me_left,
        ME_right=me_right,
        Q_discriminant=q_disc,
        residual=residual,
    )


def antipodal_distance_from_five_unfoldings(
    A: float, B: float, C: float, x: float, y: float
) -> tuple[float, tuple[float, float, float, float, float]]:
    """Distance between (x,y,0) and (A-x,B-y,C), for sorted A<=B<=C."""
    squared = (
        (A + C) ** 2 + (B - 2.0 * y) ** 2,
        (B + C) ** 2 + (A - 2.0 * x) ** 2,
        (C + x + y) ** 2 + (A + B - x - y) ** 2,
        (A + B) ** 2 + (C + 2.0 * y) ** 2,
        (A + B) ** 2 + (C + 2.0 * x) ** 2,
    )
    lengths = tuple(math.sqrt(v) for v in squared)
    return min(lengths), lengths  # type: ignore[return-value]


def _parse_triplet(text: str) -> tuple[float, float, float]:
    parts = [part.strip() for part in text.split(",")]
    if len(parts) != 3:
        raise argparse.ArgumentTypeError("Expected three comma-separated numbers.")
    try:
        return tuple(float(part) for part in parts)  # type: ignore[return-value]
    except ValueError as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("edges", type=_parse_triplet, help="edge lengths, e.g. 1,1,2")
    parser.add_argument(
        "--vertex",
        type=_parse_triplet,
        default=None,
        help="selected vertex coordinates for the fixed-vertex problem",
    )
    args = parser.parse_args()

    fixed = fixed_vertex_farthest(args.edges, args.vertex)
    diameter = intrinsic_diameter(args.edges)
    print(json.dumps({"fixed_vertex": asdict(fixed), "diameter": asdict(diameter)}, indent=2))


if __name__ == "__main__":
    main()
