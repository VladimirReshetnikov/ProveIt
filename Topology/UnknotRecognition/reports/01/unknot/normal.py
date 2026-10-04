"""Compressed normal coordinates dual to an integer simplicial 1-cocycle.

The domain is an ordinary simplicial tetrahedral complex (globally named
vertices), NOT a Regina-style face-pairing triangulation with identified local
vertices. Manifoldness/orientability is a caller precondition for interpreting
the result as a surface in an orientable 3-manifold. Coordinates can be computed
and face matching checked even when that topological precondition is not met.
No connected-component extraction, AHT orbit algorithm, or cutting is hidden here.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Mapping, Sequence

QUADS = ((0, 1), (0, 2), (0, 3))  # the other two vertices form the other side


@dataclass(frozen=True)
class NormalCoordinates:
    tetrahedra: tuple[tuple[int, int, int, int], ...]
    coordinates: tuple[tuple[int, int, int, int, int, int, int], ...]

    def face_arcs(self, tetrahedron: int, face: tuple[int, int, int]) -> dict[int, int]:
        """Arc counts on a face, indexed by its isolated global vertex."""
        tetra = self.tetrahedra[tetrahedron]
        values = self.coordinates[tetrahedron]
        if len(set(face)) != 3 or not set(face) <= set(tetra):
            raise ValueError("face is not a face of the specified tetrahedron")
        local = {tetra.index(v) for v in face}
        result = {v: values[tetra.index(v)] for v in face}
        for q, pair in enumerate(QUADS):
            part = local & set(pair)
            isolated = part if len(part) == 1 else local - part
            v = next(iter(isolated))
            result[tetra[v]] += values[4 + q]
        return result

    def check_matching(self) -> bool:
        faces: dict[tuple[int, int, int], list[int]] = {}
        for i, tetra in enumerate(self.tetrahedra):
            for face in combinations(tetra, 3):
                faces.setdefault(tuple(sorted(face)), []).append(i)
        for face, incident in faces.items():
            if len(incident) > 2:
                return False
            if len(incident) == 2:
                i, j = incident
                if self.face_arcs(i, face) != self.face_arcs(j, face):
                    return False
        return True


def from_cocycle(tetrahedra: Sequence[Sequence[int]],
                 cocycle: Mapping[tuple[int, int], int]) -> NormalCoordinates:
    """Coordinates in order T0,T1,T2,T3,Q01|23,Q02|13,Q03|12.

    Cocycle keys (u,v) have u<v; omitted edge coefficients are zero. In each
    tetrahedron the affine map to R/Z lifts to integer vertex potentials.
    Intersect its lift with half-integer levels; gaps of sorted potentials give
    sheet multiplicities without ever enumerating individual sheets.
    """
    tets = []
    for tetra in tetrahedra:
        if len(tetra) != 4 or any(type(v) is not int or v < 0 for v in tetra):
            raise ValueError("tetrahedra must have four nonnegative integer vertices")
        if len(set(tetra)) != 4:
            raise ValueError("tetrahedra must have four distinct vertices")
        tets.append(tuple(tetra))
    if len({tuple(sorted(t)) for t in tets}) != len(tets):
        raise ValueError("duplicate tetrahedron")
    edges = {tuple(sorted(e)) for t in tets for e in combinations(t, 2)}
    for edge, value in cocycle.items():
        if (not isinstance(edge, tuple) or len(edge) != 2
                or any(type(v) is not int for v in edge) or edge[0] >= edge[1]
                or edge not in edges or type(value) is not int):
            raise ValueError("cocycle keys must be ordered complex edges with integer values")

    def c(u: int, v: int) -> int:
        return cocycle.get((u, v), 0) if u < v else -cocycle.get((v, u), 0)

    coordinates = []
    incidence: dict[tuple[int, int, int], int] = {}
    for tetra in tets:
        for face in combinations(tetra, 3):
            u, v, w = face
            if c(u, v) + c(v, w) != c(u, w):
                raise ValueError("input is not a closed integral 1-cocycle")
            key = tuple(sorted(face))
            incidence[key] = incidence.get(key, 0) + 1
            if incidence[key] > 2:
                raise ValueError("more than two tetrahedra meet a face")
        heights = [0] + [c(tetra[0], v) for v in tetra[1:]]
        order = sorted(range(4), key=lambda i: (heights[i], i))
        values = [0] * 7
        values[order[0]] = heights[order[1]] - heights[order[0]]
        values[order[3]] = heights[order[3]] - heights[order[2]]
        middle = heights[order[2]] - heights[order[1]]
        low = set(order[:2])
        if 0 not in low:
            low = set(range(4)) - low
        values[4 + QUADS.index(tuple(sorted(low)))] = middle
        coordinates.append(tuple(values))
    result = NormalCoordinates(tuple(tets), tuple(coordinates))
    if not result.check_matching():
        raise ArithmeticError("normal face matching failed")
    return result
