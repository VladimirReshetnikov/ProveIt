"""Exhaustive U=1 first-descent inventory for a six-tetrahedron 3-ball.

Requires Regina's Python module.  Execute directly to emit a JSON inventory.
No unchecked moves, random choices, or recognition assumptions are used.
"""

import json
from collections import Counter

import regina


TETRAHEDRA = ["ABCD", "EBCD", "ABCX", "EBCX", "ACDY", "ECDY"]


def make_ball():
    tri = regina.Triangulation3()
    for i, _ in enumerate(TETRAHEDRA):
        tri.newTetrahedron().setDescription(f"original:{i}")
    boundary = {}
    for i, tetra in enumerate(TETRAHEDRA):
        for face in range(4):
            vertices = tuple(sorted(tetra[:face] + tetra[face + 1 :]))
            if vertices not in boundary:
                boundary[vertices] = (i, face)
                continue
            j, other_face = boundary.pop(vertices)
            permutation = [
                other_face if k == face else TETRAHEDRA[j].index(vertex)
                for k, vertex in enumerate(tetra)
            ]
            tri.tetrahedron(i).join(
                face, tri.tetrahedron(j), regina.Perm4(*permutation)
            )
    return tri


def origins(description):
    if description.startswith("original:"):
        return {int(description.split(":")[1])}
    return set(map(int, description.split(":")[2].split(",")))


def move(tri, dimension, index, stage):
    """Copy, apply a checked Pachner move, and propagate initial ancestry."""
    result = regina.Triangulation3(tri)
    face = result.face(dimension, index)
    assert result.hasPachner(face)
    consumed = {embedding.tetrahedron().index() for embedding in face.embeddings()}
    assert len(consumed) == 4 - dimension
    old_names = {t.description() for t in result.tetrahedra()}
    consumed_names = {result.tetrahedron(i).description() for i in consumed}
    source = set().union(*(origins(name) for name in consumed_names))
    assert result.pachner(face)
    fresh = [t for t in result.tetrahedra() if not t.description()]
    assert len(fresh) == dimension + 1
    assert {t.description() for t in result.tetrahedra() if t.description()} == (
        old_names - consumed_names
    )
    source_text = ",".join(map(str, sorted(source)))
    for i, tetra in enumerate(fresh):
        tetra.setDescription(f"born:{stage}.{i}:{source_text}")
    assert result.isValid()
    return result, source


def legal_moves(tri, dimension):
    return [face.index() for face in tri.faces(dimension) if tri.hasPachner(face)]


def enumerate_inventory():
    tri = make_ball()
    assert tri.isValid() and tri.isOrientable() and tri.isBall()
    assert legal_moves(tri, 1) == []
    successful = []
    all_branches = []
    for upward in legal_moves(tri, 2):
        embedding = tri.triangle(upward).embedding(0)
        parent_tetra = TETRAHEDRA[embedding.tetrahedron().index()]
        face_vertices = "".join(
            sorted(parent_tetra[embedding.vertices()[i]] for i in range(3))
        )
        after_up, up_origins = move(tri, 2, upward, 0)
        first_downward = legal_moves(after_up, 1)
        branch = {
            "up_triangle": upward,
            "up_triangle_vertices": face_vertices,
            "first_down_edges": first_downward,
            "after_first_down": [],
        }
        for first_down in first_downward:
            after_down, down_origins = move(after_up, 1, first_down, 1)
            second_downward = legal_moves(after_down, 1)
            branch["after_first_down"].append(
                {"first_down_edge": first_down, "second_down_edges": second_downward}
            )
            for second_down in second_downward:
                final, last_origins = move(after_down, 1, second_down, 2)
                source = up_origins | down_origins | last_origins
                assert final.size() == tri.size() - 1
                assert final.isBall()
                successful.append(
                    {
                        "up_triangle": upward,
                        "up_triangle_vertices": face_vertices,
                        "first_down_edge": first_down,
                        "second_down_edge": second_down,
                        "initial_footprint": sorted(source),
                        "footprint_size": len(source),
                        "final_iso_sig": final.isoSig(),
                    }
                )
        all_branches.append(branch)
    internal_edges = []
    for edge in tri.edges():
        if edge.isBoundary():
            continue
        embedding = edge.embedding(0)
        tetra_index = embedding.tetrahedron().index()
        vertices = embedding.vertices()
        letters = "".join(sorted(TETRAHEDRA[tetra_index][vertices[i]] for i in (0, 1)))
        internal_edges.append(
            {"index": edge.index(), "vertices": letters, "degree": edge.degree()}
        )
    assert successful
    assert len(successful) == 4
    assert all(item["footprint_size"] == 6 for item in successful)
    return {
        "regina_version": regina.versionString(),
        "initial_tetrahedra": TETRAHEDRA,
        "initial_iso_sig": tri.isoSig(),
        "initial_valid": tri.isValid(),
        "initial_orientable": tri.isOrientable(),
        "initial_ball": tri.isBall(),
        "internal_edges": internal_edges,
        "initial_downward_moves": [],
        "upward_candidates": len(all_branches),
        "all_branches": all_branches,
        "successful_traces": successful,
        "successful_trace_count": len(successful),
        "footprint_histogram": dict(Counter(item["footprint_size"] for item in successful)),
        "minimum_footprint": min(item["footprint_size"] for item in successful),
    }


if __name__ == "__main__":
    print(json.dumps(enumerate_inventory(), indent=2))
