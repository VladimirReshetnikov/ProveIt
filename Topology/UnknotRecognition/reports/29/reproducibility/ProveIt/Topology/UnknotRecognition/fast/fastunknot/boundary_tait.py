"""Checked cut-face Tait graphs for boundary-only completion queries.

Vertices are black *cut-face fragments*, not whole faces of the original PD.
A completion identifies only fragments touching the frontier. Its coverage,
inherited coloring, sphere Euler equation, projection components, link
components and zero-smoothing circles are checked using boundary summaries.
The resulting canonical partition can be passed to ModularTerminalKernel.

A failed inherited-color check is an explicit decline; some other classical
pairings can require recoloring a cut component. A failed sphere check is an
invalid completion. Neither case produces an invariant or a knot verdict.
This module has no report-directory or research-prototype imports.
"""
from .boundary_connectivity import BoundaryConnectivity
from .diagram import DisjointSet


def _noop():
    pass


def _rot(dart):
    return (dart & -4) | ((dart + 1) & 3)


class BoundaryDeclined(ValueError):
    """A completion does not preserve the inherited checkerboard colors."""


class _Palette:
    """Read-only checked coloring token; it also supports sequence access."""
    __slots__ = ("pd", "colors")

    def __init__(self, pd, colors):
        object.__setattr__(self, "pd", pd)
        object.__setattr__(self, "colors", tuple(colors))

    def __setattr__(self, name, value):
        raise AttributeError("checkerboard palette is immutable")

    def __delattr__(self, name):
        raise AttributeError("checkerboard palette is immutable")

    def __len__(self):
        return len(self.colors)

    def __getitem__(self, index):
        return self.colors[index]

    def __iter__(self):
        return iter(self.colors)


def _source(pd, check):
    """Validate a closed spherical PD, allowing multiple link components."""
    check()
    rows, pending, paired = [], {}, set()
    alpha = []
    for i, row in enumerate(pd):
        check()
        values = []
        for value in row:
            check()
            if type(value) is not int:
                raise ValueError("PD labels must be integers")
            values.append(value)
        if len(values) != 4:
            raise ValueError("each PD crossing must have four labels")
        rows.append(tuple(values))
        alpha.extend((-1, -1, -1, -1))
        for j, label in enumerate(values):
            check()
            dart = 4 * i + j
            if label in paired:
                raise ValueError("every original PD label must occur exactly twice")
            if label in pending:
                other = pending.pop(label)
                alpha[dart], alpha[other] = other, dart
                paired.add(label)
            else:
                pending[label] = dart
    if pending:
        raise ValueError("every original PD label must occur exactly twice")
    # Preserve immutable Diagram.pd identity so a palette can be reused cheaply.
    immutable = type(pd) is tuple
    if immutable:
        for row in pd:
            check()
            if type(row) is not tuple:
                immutable = False
                break
    rows = pd if immutable else tuple(rows)
    face, face_count = [-1] * len(alpha), 0
    for start in range(len(alpha)):
        check()
        if face[start] >= 0:
            continue
        dart = start
        while face[dart] < 0:
            check()
            face[dart] = face_count
            dart = _rot(alpha[dart])
        if dart != start:
            raise ValueError("original face walk does not close")
        face_count += 1
    projection = DisjointSet(len(rows))
    for dart, other in enumerate(alpha):
        check()
        projection.union(dart // 4, other // 4)
    components = set()
    for i in range(len(rows)):
        check()
        components.add(projection.find(i))
    if face_count != len(rows) + 2 * len(components):
        raise ValueError("original PD rotation system is not spherical")
    return rows, alpha, face, face_count


def coloring(pd, check=None):
    """Return an immutable reusable palette for a checked spherical source PD."""
    check = _noop if check is None else check
    rows, alpha, face, face_count = _source(pd, check)
    adjacent = []
    for _ in range(face_count):
        check()
        adjacent.append(set())
    for dart, other in enumerate(alpha):
        check()
        adjacent[face[dart]].add(face[other])
    color = [-1] * face_count
    for start in range(face_count):
        check()
        if color[start] >= 0:
            continue
        color[start] = 0
        queue = [start]
        for f in queue:
            check()
            for g in adjacent[f]:
                check()
                if color[g] < 0:
                    color[g] = 1 - color[f]
                    queue.append(g)
                elif color[g] == color[f]:
                    raise ValueError("original faces are not checkerboard colorable")
    colors = []
    for f in face:
        check()
        colors.append(color[f])
    check()
    return _Palette(rows, colors)


def _checked_palette(pd, palette, check):
    if palette is None:
        return coloring(pd, check)
    if isinstance(palette, _Palette) and palette.pd is pd:
        check()
        return palette
    rows, alpha, face, face_count = _source(pd, check)
    colors = []
    for color in palette:
        check()
        if type(color) is not int or color not in (0, 1):
            raise ValueError("palette entries must be 0 or 1")
        colors.append(color)
    if len(colors) != len(alpha):
        raise ValueError("palette must color every original dart")
    face_colors = [-1] * face_count
    for dart, other in enumerate(alpha):
        check()
        f = face[dart]
        if face_colors[f] >= 0 and face_colors[f] != colors[dart]:
            raise ValueError("palette changes color inside an original face")
        face_colors[f] = colors[dart]
        if colors[dart] == colors[other]:
            raise ValueError("palette does not checkerboard adjacent faces")
    check()
    return _Palette(rows, colors)


class BoundaryTait:
    """A checked fixed suffix and the Tait graph common to accepted closures.

    ``order`` is a permutation of all source crossings; ``stage`` is a proper
    prefix length. Reuse ``palette`` from ``coloring`` or a previous instance to
    avoid recoloring an immutable source. Setup uses a dense integer Laplacian;
    geometry itself is linear apart from sorting and disjoint-set operations.
    ``partition`` uses only the frontier, not the stored suffix crossings.
    """

    def __init__(self, pd, order, stage, palette=None, check=None):
        check = _noop if check is None else check
        check()
        palette = _checked_palette(pd, palette, check)
        pd = palette.pd
        crossing_order, used = [], set()
        for index in order:
            check()
            if (type(index) is not int or not 0 <= index < len(pd)
                    or index in used):
                raise ValueError("order must be a permutation of source crossings")
            crossing_order.append(index)
            used.add(index)
        if len(crossing_order) != len(pd):
            raise ValueError("order must cover every source crossing")
        if type(stage) is not int or not 0 <= stage < len(crossing_order):
            raise ValueError("boundary Tait geometry requires a nonempty suffix")
        n = len(crossing_order) - stage
        colors, alpha, boundary = [], [-1] * (4 * n), {}
        for k in range(n):
            check()
            index = crossing_order[stage + k]
            for j, label in enumerate(pd[index]):
                check()
                colors.append(palette[4 * index + j])
                dart = 4 * k + j
                if label in boundary:
                    other = boundary.pop(label)
                    alpha[dart], alpha[other] = other, dart
                else:
                    boundary[label] = dart
        connectivity = BoundaryConnectivity(alpha, boundary, check)
        faces, projection = DisjointSet(4 * n), DisjointSet(n)
        for dart, other in enumerate(alpha):
            check()
            if other >= 0:
                faces.union(dart, _rot(other))
                projection.union(dart // 4, other // 4)
        face_roots, face_colors = set(), {}
        for dart, color in enumerate(colors):
            check()
            root = faces.find(dart)
            face_roots.add(root)
            if root in face_colors and face_colors[root] != color:
                raise ValueError("cut face changes original color")
            face_colors[root] = color
        black_count = 0
        for color in face_colors.values():
            check()
            black_count += color
        if black_count > len(face_colors) // 2:
            for i in range(len(colors)):
                check()
                colors[i] = 1 - colors[i]
            for root in face_colors:
                check()
                face_colors[root] = 1 - face_colors[root]
        ends, starts, open_roots = {}, {}, set()
        for label, dart in boundary.items():
            check()
            end, start = faces.find(dart), faces.find(_rot(dart))
            ends[label], starts[label] = end, start
            open_roots.update((end, start))
        check()
        open_faces = sorted(open_roots)
        check()
        face_ids, open_colors = {}, []
        for i, root in enumerate(open_faces):
            check()
            face_ids[root] = i
            open_colors.append(face_colors[root])
        for label in boundary:
            check()
            ends[label], starts[label] = face_ids[ends[label]], face_ids[starts[label]]
        black = []
        for root in face_roots:
            check()
            if face_colors[root]:
                black.append(root)
        check()
        black.sort()
        check()
        black_ids = {}
        for i, root in enumerate(black):
            check()
            black_ids[root] = i
        terminals, black_open = [], []
        for root in open_faces:
            check()
            if face_colors[root]:
                terminals.append(black_ids[root])
                black_open.append(face_ids[root])
        closed_black = len(black) - len(terminals)
        if not terminals:
            terminals = [0]  # Empty frontier: retain a grounding vertex.
        edges, b_total = [], 0
        for base in range(0, 4 * n, 4):
            check()
            slots = []
            for j in range(4):
                check()
                if colors[base + j]:
                    slots.append(j)
            if slots not in ([0, 2], [1, 3]):
                raise ValueError("invalid checkerboard sectors at a crossing")
            u = black_ids[faces.find(base + slots[0])]
            v = black_ids[faces.find(base + slots[1])]
            b = int(slots == [0, 2])
            b_total += b
            edges.append((u, v, -1 if b else 1))
        laplacian = []
        for _ in black:
            check()
            row = []
            for _ in black:
                check()
                row.append(0)
            laplacian.append(row)
        for u, v, weight in edges:
            check()
            if u != v:
                laplacian[u][u] += weight
                laplacian[v][v] += weight
                laplacian[u][v] -= weight
                laplacian[v][u] -= weight
        projection_roots, open_projection = set(), set()
        for i in range(n):
            check()
            projection_roots.add(projection.find(i))
        for dart in boundary.values():
            check()
            open_projection.add(projection.find(dart // 4))
        check()
        ordered_projection = sorted(open_projection)
        check()
        projection_ids = {}
        for i, root in enumerate(ordered_projection):
            check()
            projection_ids[root] = i
        projection_labels = {}
        for label, dart in boundary.items():
            check()
            projection_labels[label] = projection_ids[projection.find(dart // 4)]
        frozen_laplacian = []
        for row in laplacian:
            check()
            frozen_laplacian.append(tuple(row))
        check()
        self.n = n
        self.palette = palette
        self.labels = connectivity.labels
        self.boundary = boundary
        self.connectivity = connectivity
        self.ends, self.starts = ends, starts
        self.open_colors = tuple(open_colors)
        self.closed_faces = len(face_roots) - len(open_faces)
        self.black_open = tuple(black_open)
        self.closed_black = closed_black
        self.terminals = tuple(terminals)
        self.edges = tuple(edges)
        self.laplacian = tuple(frozen_laplacian)
        self.B = b_total
        self.projection = projection_labels
        self.closed_projection = len(projection_roots) - len(ordered_projection)
        self.projection_size = len(ordered_projection)

    def partition(self, pairs, check=None):
        """Verify a closure and return a canonical terminal partition and phase.

        The phase exponent specifies ``(-i)**phase`` multiplying the signed
        tree cofactor. Disconnected projections have zero reduced q=i value.
        ``unreduced_euler`` is the exact signed q=1 Euler characteristic.
        """
        check = _noop if check is None else check
        check()
        matching = []
        for pair in pairs:
            check()
            values = []
            for label in pair:
                check()
                if type(label) is not int:
                    raise ValueError("matching labels must be integers")
                values.append(label)
            if len(values) != 2:
                raise ValueError("matching entries must be pairs")
            matching.append(tuple(values))
        components, zero = self.connectivity.counts(matching, check)
        faces = DisjointSet(len(self.open_colors))
        projection = DisjointSet(self.projection_size)
        for a, b in matching:
            check()
            for end, start in ((self.ends[a], self.starts[b]),
                               (self.ends[b], self.starts[a])):
                check()
                if self.open_colors[end] != self.open_colors[start]:
                    raise BoundaryDeclined("matching changes inherited face colors")
                faces.union(end, start)
            projection.union(self.projection[a], self.projection[b])
        projection_roots = set()
        for i in range(self.projection_size):
            check()
            projection_roots.add(projection.find(i))
        shadows = self.closed_projection + len(projection_roots)
        face_roots = set()
        for i in range(len(self.open_colors)):
            check()
            face_roots.add(faces.find(i))
        face_count = self.closed_faces + len(face_roots)
        if face_count != self.n + 2 * shadows:
            raise ValueError("matching completion is not spherical")
        names, partition = {}, []
        for i in self.black_open:
            check()
            root = faces.find(i)
            partition.append(names.setdefault(root, len(names)))
        vertices = self.closed_black + len(names)
        check()
        return dict(partition=tuple(partition) or (0,),
                    phase=(self.B + vertices - 1) % 4,
                    black_vertices=vertices, shadow_components=shadows,
                    link_components=components, zero_circles=zero,
                    unreduced_euler=(-1 if (self.n + components + zero) % 2 else 1)
                                    * (1 << components))
