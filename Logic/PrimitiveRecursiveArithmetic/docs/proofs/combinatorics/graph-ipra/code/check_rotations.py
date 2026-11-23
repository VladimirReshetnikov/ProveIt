"""Check nonloop contractions and dual spanning trees on small orientable maps.

Enumerates all connected rotation permutations of 2m darts, with m = 1, 2, 3
and the fixed edge involution 0↔1, 2↔3, ... . Different dart labellings are
retained. Run with Python 3, without external packages.
"""
from itertools import combinations, permutations


def cycles(permutation):
    """List the nonempty orbits of a permutation represented as a dictionary."""
    result = []
    seen = set()
    for start in permutation:
        if start in seen:
            continue
        orbit = []
        current = start
        while current not in seen:
            seen.add(current)
            orbit.append(current)
            current = permutation[current]
        result.append(orbit)
    return result


def from_cycles(orbits):
    return {dart: orbit[(i + 1) % len(orbit)]
            for orbit in orbits for i, dart in enumerate(orbit)}


def component_count(n, edges):
    blocks = [{i} for i in range(n)]
    for u, v in edges:
        left = next(block for block in blocks if u in block)
        right = next(block for block in blocks if v in block)
        if left != right:
            left.update(right)
            blocks.remove(right)
    return len(blocks)


def starting_after(orbit, dart):
    """Delete the given dart and linearize the cyclic order after its place."""
    i = orbit.index(dart)
    return orbit[i + 1:] + orbit[:i]


def face_permutation(rotation):
    return {dart: rotation[dart ^ 1] for dart in rotation}


def check_contraction(e, u, v, vertices, old_faces, face_count):
    first, second = 2 * e, 2 * e + 1
    merged = starting_after(vertices[u], first) + starting_after(vertices[v], second)
    untouched = [orbit for i, orbit in enumerate(vertices) if i not in (u, v)]
    reduced = face_permutation(from_cycles(untouched + [merged]))
    # Independent face successor from the original map: skip both removed darts.
    for dart, successor in reduced.items():
        expected = old_faces[dart]
        while expected in (first, second):
            expected = old_faces[expected]
        assert successor == expected, (old_faces, e, dart)
    # Contracting a one-edge component produces one isolated vertex/empty face.
    assert max(1, len(cycles(reduced))) == face_count, (old_faces, e)


def check_dual_trees(edges, n, face_of, face_count):
    checks = 0
    for tree in combinations(range(len(edges)), n - 1):
        if component_count(n, [edges[e] for e in tree]) != 1:
            continue
        dual_edges = [(face_of[2 * e], face_of[2 * e + 1])
                      for e in range(len(edges)) if e not in tree]
        assert len(dual_edges) == face_count - 1, (edges, tree)
        assert component_count(face_count, dual_edges) == 1, (edges, tree)
        checks += 1
    return checks


def main():
    maps = contractions = dual_trees = 0
    for m in range(1, 4):
        for successor_tuple in permutations(range(2 * m)):
            rotation = dict(enumerate(successor_tuple))
            vertices = cycles(rotation)
            n = len(vertices)
            vertex_of = {d: i for i, orbit in enumerate(vertices) for d in orbit}
            edges = [(vertex_of[2 * e], vertex_of[2 * e + 1]) for e in range(m)]
            if component_count(n, edges) != 1:
                continue
            maps += 1
            faces = face_permutation(rotation)
            face_orbits = cycles(faces)
            face_count = len(face_orbits)
            for e, (u, v) in enumerate(edges):
                if u != v:
                    check_contraction(e, u, v, vertices, faces, face_count)
                    contractions += 1
            if n - m + face_count == 2:
                face_of = {d: i for i, orbit in enumerate(face_orbits) for d in orbit}
                dual_trees += check_dual_trees(edges, n, face_of, face_count)
    print(f'{maps} connected rotations, {contractions} nonloop contractions, '
          f'{dual_trees} dual spanning-tree complements verified.')


if __name__ == '__main__':
    main()
