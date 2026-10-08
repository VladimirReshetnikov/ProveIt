"""Deterministic spherical ribbon-graph fixtures and random test generators."""
from __future__ import annotations

from itertools import combinations
import random
from typing import Iterable


def dual_of_triangles(faces: Iterable[tuple[int, int, int]]) -> dict:
    """Convert an oriented closed triangular sphere to its cubic ribbon dual.

    Repeated faces (the two opposite sides of K3) are permitted; repeated
    vertices in a face are not.  The production validator checks the sphere.
    """
    faces = list(faces)
    incidence: dict[tuple[int, int], list[tuple[int, int, int, int]]] = {}
    for f, (a, b, c) in enumerate(faces):
        if len({a, b, c}) != 3:
            raise ValueError("face vertices must be distinct")
        for corner, (u, v) in enumerate(((a, b), (b, c), (c, a))):
            incidence.setdefault(tuple(sorted((u, v))), []).append((f, corner, u, v))
    rotation = [[-1] * 3 for _ in faces]
    for edge, key in enumerate(sorted(incidence)):
        locations = incidence[key]
        if len(locations) != 2:
            raise ValueError("every edge must have exactly two incident faces")
        (f, i, a, b), (g, j, c, d) = locations
        if (a, b) != (d, c):
            raise ValueError("adjacent face orientations are inconsistent")
        rotation[f][i], rotation[g][j] = 2 * edge, 2 * edge + 1
    return {"ambient": "3-ball", "rotation": rotation, "circles": 0}


def bipyramid_faces(ring: int) -> list[tuple[int, int, int]]:
    if ring < 3:
        raise ValueError("a bipyramid requires a ring of at least three vertices")
    faces = []
    for i in range(ring):
        a, b = 2 + i, 2 + (i + 1) % ring
        faces.extend(((0, a, b), (1, b, a)))
    return faces


def bipyramid(ring: int) -> dict:
    return dual_of_triangles(bipyramid_faces(ring))


def triangle() -> dict:
    return dual_of_triangles([(0, 1, 2), (0, 2, 1)])


def tetrahedron_faces() -> list[tuple[int, int, int]]:
    return [(0, 2, 1), (0, 1, 3), (1, 2, 3), (2, 0, 3)]


def tetrahedron() -> dict:
    return dual_of_triangles(tetrahedron_faces())


def random_triangulation(vertices: int, seed: int, flips: int = 0) -> dict:
    if vertices < 4:
        raise ValueError("at least four vertices required")
    rng = random.Random(seed)
    faces = tetrahedron_faces()
    for v in range(4, vertices):
        i = rng.randrange(len(faces))
        a, b, c = faces.pop(i)
        faces.extend(((a, b, v), (b, c, v), (c, a, v)))
    for _ in range(flips):
        incidence: dict[tuple[int, int], list[tuple[int, int, int, int]]] = {}
        for index, face in enumerate(faces):
            for j in range(3):
                a, b, c = face[j], face[(j + 1) % 3], face[(j + 2) % 3]
                incidence.setdefault(tuple(sorted((a, b))), []).append((index, a, b, c))
        first, second = rng.choice(list(incidence.values()))
        i, a, b, c = first
        j, _, _, d = second
        if c == d or tuple(sorted((c, d))) in incidence:
            continue
        faces[i], faces[j] = (c, a, d), (d, b, c)
    return dual_of_triangles(faces)


def disjoint_union(*patterns: dict, circles: int = 0) -> dict:
    rotation = []
    for pattern in patterns:
        offset = 3 * len(rotation)
        rotation.extend([[d + offset for d in row] for row in pattern["rotation"]])
        circles += pattern.get("circles", 0)
    return {"ambient": "3-ball", "rotation": rotation, "circles": circles}


def dumbbell() -> dict:
    return {"ambient": "3-ball", "rotation": [[0, 2, 3], [1, 4, 5]], "circles": 0}


def two_edge_bond() -> dict:
    return {"ambient": "3-ball",
            "rotation": [[8, 0, 2], [10, 3, 1], [9, 4, 6], [11, 7, 5]],
            "circles": 0}


def perfect_matchings(items: tuple[int, ...]):
    if not items:
        yield ()
        return
    first = items[0]
    for i in range(1, len(items)):
        second = items[i]
        rest = items[1:i] + items[i + 1:]
        for matching in perfect_matchings(rest):
            yield ((first, second),) + matching


def pattern_from_matching(vertices: int, matching) -> dict:
    darts = [-1] * (3 * vertices)
    for e, (a, b) in enumerate(matching):
        darts[a], darts[b] = 2 * e, 2 * e + 1
    return {"ambient": "3-ball",
            "rotation": [darts[3 * v:3 * v + 3] for v in range(vertices)],
            "circles": 0}


def random_matching_pattern(vertices: int, rng: random.Random) -> dict:
    darts = list(range(3 * vertices))
    rng.shuffle(darts)
    return pattern_from_matching(vertices, list(zip(darts[::2], darts[1::2])))


def relabel_pattern(pattern: dict, seed: int, mirror: bool = False) -> dict:
    """Change edge labels, edge directions and vertex order without topology."""
    rng = random.Random(seed)
    n = 3 * len(pattern["rotation"]) // 2
    permutation = list(range(n))
    rng.shuffle(permutation)
    reverse = [rng.randrange(2) for _ in range(n)]
    rows = []
    for row in pattern["rotation"]:
        renamed = [2 * permutation[d // 2] + ((d % 2) ^ reverse[d // 2]) for d in row]
        if mirror:
            renamed.reverse()
        k = rng.randrange(3)
        rows.append(renamed[k:] + renamed[:k])
    rng.shuffle(rows)
    return {"ambient": "3-ball", "rotation": rows, "circles": pattern.get("circles", 0)}
