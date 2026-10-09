"""Legal simplicial moves for geometric stress fixtures, not a knot simplifier."""
from dataclasses import dataclass, asdict
from itertools import combinations
from .geometry import SolidTorus


@dataclass(frozen=True)
class MeshFixture:
    n: int
    tetrahedra: tuple[tuple[int, ...], ...]
    heights: tuple[tuple[int, ...], ...]
    generator_edges: tuple[tuple[int, int], ...]
    history: tuple[dict, ...]
    incidence = SolidTorus.incidence
    model = SolidTorus.model

    def to_dict(self):
        return asdict(self)


def from_product(g):
    return MeshFixture(g.n, g.tetrahedra, g.heights, g.generator_edges,
                       ({'move': 'product', 'segments': g.segments,
                         'central_vertex': g.disk_vertices == 4},))


def moves23(g):
    faces, edges, _ = g.incidence()
    for face, inc in sorted(faces.items()):
        if len(inc) != 2:
            continue
        a, b = inc[0][0], inc[1][0]
        x = next(v for v in g.tetrahedra[a] if v not in face)
        y = next(v for v in g.tetrahedra[b] if v not in face)
        if x != y and tuple(sorted((x, y))) not in edges:
            yield tuple(face)


def move23(g, face):
    face = tuple(sorted(face))
    faces, edges, _ = g.incidence()
    if face not in faces or len(faces[face]) != 2:
        raise ValueError("2-3 move requires an interior triangular face")
    a, b = faces[face][0][0], faces[face][1][0]
    x = next(v for v in g.tetrahedra[a] if v not in face)
    y = next(v for v in g.tetrahedra[b] if v not in face)
    if x == y or tuple(sorted((x, y))) in edges:
        raise ValueError("new edge already exists or opposite vertices coincide")
    ha = dict(zip(g.tetrahedra[a], g.heights[a]))
    hb = dict(zip(g.tetrahedra[b], g.heights[b]))
    shift = ha[face[0]]-hb[face[0]]
    if any(ha[v] != hb[v]+shift for v in face):
        raise ValueError("face heights fail constant-transition check")
    h = ha | {y: hb[y]+shift}
    tets = [t for i, t in enumerate(g.tetrahedra) if i not in (a, b)]
    heights = [t for i, t in enumerate(g.heights) if i not in (a, b)]
    for u, v in combinations(face, 2):
        tet = (x, y, u, v)
        tets.append(tet);heights.append(tuple(h[z] for z in tet))
    out = MeshFixture(g.n, tuple(tets), tuple(heights), g.generator_edges,
                      g.history+({'move': '2-3', 'face': list(face)},))
    out.incidence()
    return out


def move14(g, index, height=None):
    if type(index) is not int or not 0 <= index < len(g.tetrahedra):
        raise ValueError("invalid tetrahedron index")
    vs, hs = g.tetrahedra[index], g.heights[index]
    height = min(hs) if height is None else height
    if type(height) is not int:
        raise ValueError("integral stellar height required")
    h = dict(zip(vs, hs)) | {g.n: height}
    tets = [t for i, t in enumerate(g.tetrahedra) if i != index]
    heights = [t for i, t in enumerate(g.heights) if i != index]
    for face in combinations(vs, 3):
        tet = (g.n,)+face
        tets.append(tet);heights.append(tuple(h[z] for z in tet))
    out = MeshFixture(g.n+1, tuple(tets), tuple(heights), g.generator_edges,
                      g.history+({'move': '1-4', 'tetrahedron': index, 'height': height},))
    out.incidence()
    return out


def replay_history(history):
    from .geometry import product_solid_torus
    first = history[0]
    if first['move'] != 'product':
        raise ValueError("expected a product source")
    g = from_product(product_solid_torus(first['segments'], first['central_vertex']))
    for row in history[1:]:
        if row['move'] == '2-3':
            g = move23(g, row['face'])
        elif row['move'] == '1-4':
            g = move14(g, row['tetrahedron'], row['height'])
        else:
            raise ValueError("unsupported fixture move")
    return g
