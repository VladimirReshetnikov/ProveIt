#!/usr/bin/env python3
"""Exact finite checks accompanying the constructive Gauss--Bonnet report.

This is a transparent reference implementation, not a proof of correctness
of Python and not a replacement for an iPRA/Lean derivation. It uses only
integer and Fraction arithmetic. Run directly for the supplied examples.
"""

from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as Q
import json


@dataclass(frozen=True)
class Mesh:
    faces: tuple[tuple[int, int, int], ...]

    def inspect(self, require_coherent_orientation=False):
        """Check a finite simplicial 2-manifold with boundary.

        The graph walks are bounded by the supplied finite vertex/edge lists;
        all operations have straightforward PR implementations. The input may
        have several connected components and may be nonorientable. Isolated
        vertices are not included. A coherent orientation is an optional
        stronger certificate, unnecessary for the inward-conormal formula.
        """
        if not self.faces:
            raise ValueError("the example format requires at least one face")
        edge_occ = defaultdict(list)
        link_edges = defaultdict(list)
        corners = defaultdict(list)
        seen_faces = set()
        vertices = set()
        for fi, face in enumerate(self.faces):
            if len(face) != 3 or len(set(face)) != 3:
                raise ValueError("each face has three distinct vertices")
            if any(type(v) is not int or v < 0 for v in face):
                raise ValueError("vertex labels must be natural numbers")
            key = tuple(sorted(face))
            if key in seen_faces:
                raise ValueError("duplicate unoriented face")
            seen_faces.add(key)
            vertices.update(face)
            for j, v in enumerate(face):
                a, b = face[j], face[(j + 1) % 3]
                edge_occ[tuple(sorted((a, b)))].append((fi, j, a, b))
                link_edges[v].append((face[(j + 1) % 3], face[(j + 2) % 3]))
                corners[v].append((fi, j))
        boundary_edges, interior_edges = [], []
        orientation_graph = defaultdict(list)
        coherently_oriented = True
        for key, occurrences in sorted(edge_occ.items()):
            if len(occurrences) == 1:
                boundary_edges.append(key)
            elif len(occurrences) == 2:
                a, b = occurrences
                opposite = a[2:] == b[2:][::-1]
                coherently_oriented = coherently_oriented and opposite
                if require_coherent_orientation and not opposite:
                    raise ValueError("paired edge orientations do not cancel")
                sign = 1 if opposite else -1
                orientation_graph[a[0]].append((b[0], sign))
                orientation_graph[b[0]].append((a[0], sign))
                interior_edges.append(key)
            else:
                raise ValueError("edge has neither one nor two incident faces")
        face_signs = {}
        orientable = True
        for fi in range(len(self.faces)):
            if fi in face_signs:
                continue
            face_signs[fi] = 1
            stack = [fi]
            for _ in range(len(self.faces) + 1):
                if not stack:
                    break
                f0 = stack.pop()
                for f1, sign in orientation_graph[f0]:
                    required = face_signs[f0] * sign
                    if f1 in face_signs:
                        orientable = orientable and face_signs[f1] == required
                    else:
                        face_signs[f1] = required
                        stack.append(f1)
        boundary_vertices = set(v for e in boundary_edges for v in e)
        for v in sorted(vertices):
            adj = defaultdict(set)
            for a, b in link_edges[v]:
                adj[a].add(b)
                adj[b].add(a)
            start = min(adj)
            reached, stack = set(), [start]
            for _ in range(len(adj) + len(link_edges[v]) + 1):
                if not stack:
                    break
                x = stack.pop()
                if x not in reached:
                    reached.add(x)
                    stack.extend(y for y in sorted(adj[x]) if y not in reached)
            if reached != set(adj):
                raise ValueError("vertex link is disconnected")
            degrees = [len(adj[x]) for x in adj]
            if v in boundary_vertices:
                if degrees.count(1) != 2 or any(d not in (1, 2) for d in degrees):
                    raise ValueError("boundary vertex link is not a path")
            elif any(d != 2 for d in degrees):
                raise ValueError("interior vertex link is not a cycle")
        vi = len(vertices - boundary_vertices)
        vb = len(boundary_vertices)
        ei, eb, f = len(interior_edges), len(boundary_edges), len(self.faces)
        if 3 * f != 2 * ei + eb or eb != vb:
            raise AssertionError("a valid surface must satisfy both incidence identities")
        return {
            "vertices": vertices,
            "boundary_vertices": boundary_vertices,
            "edge_occurrences": edge_occ,
            "corners": corners,
            "interior_edges": interior_edges,
            "boundary_edges": boundary_edges,
            "counts": {"Vi": vi, "Vb": vb, "Ei": ei, "Eb": eb, "F": f},
            "chi": vi + vb - ei - eb + f,
            "orientable": orientable,
            "coherently_oriented": coherently_oriented,
        }


def exact_assembly(mesh, p, curvature, halfedge, angles, exterior):
    """Check the exact residual identity for arbitrary rational values.

    halfedge[(f,j)] integrates along face edge j -> j+1;
    angles[(f,j)] is the angle at face vertex j;
    exterior[v] is a signed exterior angle at a boundary vertex.
    """
    d = mesh.inspect()
    counts = d["counts"]
    f = counts["F"]
    slots = {(i, j) for i in range(f) for j in range(3)}
    if len(curvature) != f or set(halfedge) != slots or set(angles) != slots:
        raise ValueError("incorrect face, edge, or corner table shape")
    if set(exterior) != d["boundary_vertices"]:
        raise ValueError("one exterior angle is required per boundary vertex")
    C = sum(curvature, Q(0))
    B = sum((halfedge[occ[0][:2]] for e in d["boundary_edges"]
             for occ in [d["edge_occurrences"][e]]), Q(0))
    edge_residual = {
        e: sum((halfedge[o[:2]] for o in d["edge_occurrences"][e]), Q(0))
        for e in d["interior_edges"]
    }
    I = sum(edge_residual.values(), Q(0))
    A = sum(angles.values(), Q(0))
    theta = sum(exterior.values(), Q(0))
    face_residual = [curvature[i] + sum(halfedge[i, j] for j in range(3))
                     + p - sum(angles[i, j] for j in range(3)) for i in range(f)]
    vertex_residual = {}
    for v in d["vertices"]:
        a = sum((angles[slot] for slot in d["corners"][v]), Q(0))
        vertex_residual[v] = (a + exterior[v] - p if v in d["boundary_vertices"]
                              else a - 2 * p)
    R = sum(face_residual, Q(0))
    S = sum(vertex_residual.values(), Q(0))
    defect = C + B + theta - 2 * p * d["chi"]
    assert R == C + B + I + f * p - A
    assert S == A + theta - (2 * counts["Vi"] + counts["Vb"]) * p
    assert defect == R - I + S
    budget = (sum(map(abs, face_residual), Q(0))
              + sum(map(abs, edge_residual.values()), Q(0))
              + sum(map(abs, vertex_residual.values()), Q(0)))
    assert abs(defect) <= budget
    return {"counts": counts, "chi": d["chi"], "orientable": d["orientable"], "defect": str(defect),
            "budget": str(budget), "identity": True}


def equilateral_polyhedral(mesh, p):
    """Exact angle-defect identity in units of a rational surrogate for pi."""
    d = mesh.inspect()
    interior_defects, boundary_turns = {}, {}
    for v in d["vertices"]:
        angle_sum = len(d["corners"][v]) * p / 3
        if v in d["boundary_vertices"]:
            boundary_turns[v] = p - angle_sum
        else:
            interior_defects[v] = 2 * p - angle_sum
    total = sum(interior_defects.values(), Q(0)) + sum(boundary_turns.values(), Q(0))
    assert total == 2 * p * d["chi"]
    return {"counts": d["counts"], "chi": d["chi"], "orientable": d["orientable"],
            "curvature_in_pi_units": str(total / p), "identity": True}


def example_meshes():
    tetra = Mesh(((0, 2, 1), (0, 1, 3), (0, 3, 2), (1, 2, 3)))
    disk = Mesh(((0, 1, 2), (0, 2, 3)))
    annulus_faces = []
    for i in range(3):
        j = (i + 1) % 3
        annulus_faces.extend(((i, j, 3 + j), (i, 3 + j, 3 + i)))
    torus_faces = []
    v = lambda i, j: 3 * (i % 3) + (j % 3)
    for i in range(3):
        for j in range(3):
            torus_faces.extend(((v(i, j), v(i + 1, j), v(i + 1, j + 1)),
                                (v(i, j), v(i + 1, j + 1), v(i, j + 1))))
    projective = Mesh(((0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 3, 5), (0, 4, 5),
                       (1, 2, 5), (1, 3, 4), (1, 4, 5), (2, 3, 4), (2, 3, 5)))
    return {"tetrahedron": tetra, "two_triangle_disk": disk,
            "annulus": Mesh(tuple(annulus_faces)), "torus": Mesh(tuple(torus_faces)),
            "projective_plane": projective}


def self_check():
    out = {"arithmetic": "exact fractions; no floating-point tolerance", "examples": {}}
    p = Q(355, 113)  # Only a rational test parameter; no pi error claim is needed.
    for name, mesh in example_meshes().items():
        d = mesh.inspect()
        f = len(mesh.faces)
        curvature = [Q((-1) ** i * (i + 1), i + 2) for i in range(f)]
        halfedge = {(i, j): Q((-1) ** (i + j) * (2 * i + j + 1), i + j + 2)
                    for i in range(f) for j in range(3)}
        angles = {(i, j): Q(i + j + 1, i + 2 * j + 3)
                  for i in range(f) for j in range(3)}
        exterior = {v: Q(v - 2, v + 3) for v in d["boundary_vertices"]}
        out["examples"][name] = {
            "arbitrary_rational_residuals": exact_assembly(mesh, p, curvature, halfedge, angles, exterior),
            "equilateral_cone_metric": equilateral_polyhedral(mesh, p),
        }
    bad = {
        "disconnected_vertex_link": Mesh(((0, 1, 2), (0, 3, 4))),
        "duplicate_face": Mesh(((0, 1, 2), (0, 2, 1))),
    }
    out["rejected_invalid_meshes"] = {}
    for name, mesh in bad.items():
        try:
            mesh.inspect()
        except ValueError as exc:
            out["rejected_invalid_meshes"][name] = str(exc)
        else:
            raise AssertionError("invalid mesh accepted: " + name)
    mismatched_disk = Mesh(((0, 1, 2), (0, 3, 2)))
    assert mismatched_disk.inspect()["orientable"]
    assert not mismatched_disk.inspect()["coherently_oriented"]
    try:
        mismatched_disk.inspect(require_coherent_orientation=True)
    except ValueError as exc:
        out["rejected_optional_orientation_certificate"] = str(exc)
    else:
        raise AssertionError("incoherent optional orientation accepted")
    assert not example_meshes()["projective_plane"].inspect()["orientable"]
    return out


if __name__ == "__main__":
    print(json.dumps(self_check(), indent=2, sort_keys=True))
