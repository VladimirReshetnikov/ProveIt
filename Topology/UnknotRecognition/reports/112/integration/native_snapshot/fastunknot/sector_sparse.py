"""Sparse construction of the existing exact quadrilateral-sector kernel.

``PreparedSectorSource`` validates one supplied triangulation and compiles its
face-corner incidences once.  Repeated sectors reuse those immutable data.  The
caller must not mutate the triangulation, the prepared source, or the shared
``prepared`` field of a returned kernel while any of them remain in use.  This
is a read-only-source contract, not a provenance claim about a knot diagram.

Every compiled equation has at most two signed quadrilateral-type incidences.
A sector scan contracts its zero-labelled equations without allocating a
length-k vector for each equation.  Only the at most 4k active equations get
dense labels.  Singleton potential components share one immutable zero tuple.
The returned object is the existing ``SectorKernel``; its combinatorial data,
potential gauge, exact cycle rows, and rational basis agree with the original
builder.  The original dense exact elimination is deliberately retained.

Before elimination, construction takes O(t log(t+1) + k**2) elementary integer
operations and O(t + k**2) integer slots.  Union by size bounds every parent
path by O(log(t+1)); path halving may improve that bound.  Sorting canonical
corner representatives is charged.  Integer slots are not unit-cost bits:
indices require O(log(t+1)) bits.  The rational elimination and the returned
basis have their additional existing costs.
"""

from .normal_sector import SectorKernel, _nullspace, _primitive, _source_hash, _support
from .normal_surface_geometry import _prepare, _quad


def _ordered_cycle_rows(rows, width, check):
    """Lexicographic order by fixed-alphabet radix sort, in O(k**2) work.

    Each quadrilateral occurs in at most four face-corner labels.  A
    fundamental cycle traverses each labelled edge at most once, so every
    primitive cycle coefficient lies in [-4, 4].  Stable radix sorting avoids
    an extra logarithm from repeated comparisons of long, zero-heavy tuples.
    """
    items = list(rows)
    if not items:
        return ()
    for column in range(width-1, -1, -1):
        check()
        buckets = [[] for _ in range(9)]
        for row in items:
            value = row[column]
            if not -4 <= value <= 4:
                raise ArithmeticError('fundamental-cycle coefficient bound failed')
            buckets[value+4].append(row)
        items = [row for bucket in buckets for row in bucket]
    return tuple(items)


class PreparedSectorSource:
    """Validated, reusable source with the read-only contract above.

    Construction and every build honor the supplied cooperative ``check``
    callback, including callable objects whose Boolean value is false.
    Interruption of a build leaves the prepared source reusable.
    """

    def __init__(self, triangulation, check=lambda: None):
        prepared = _prepare(triangulation, check)
        compiled = []
        for t, f, u, g, permutation in prepared['pairs']:
            check()
            for v in range(4):
                if v == f:
                    continue
                w = permutation[v]
                left = (t, _quad(f, v))
                right = (u, _quad(g, w))
                incidences = () if left == right else ((left, 1), (right, -1))
                compiled.append((4*t+v, 4*u+w, incidences))
        self.triangulation = triangulation
        self.prepared = prepared
        self.face_corner_equations = tuple(compiled)
        self._source_sha256 = _source_hash(triangulation)

    @property
    def source_sha256(self):
        """Digest captured at validation; consumers can bind an external source.

        This read-only property does not rehash or authorize later mutation of
        the underlying dictionary.  The read-only-source contract still holds.
        """
        return self._source_sha256

    def build(self, allowed_types, *, check=lambda: None):
        """Return the baseline-compatible kernel for one allowed support."""
        check()
        prepared = self.prepared
        count = len(prepared['tetrahedra'])
        support = _support(allowed_types, count)
        index = {item: j for j, item in enumerate(support)}
        k = len(support)
        parent = list(range(4*count))
        size = [1]*(4*count)
        least = list(range(4*count))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            a, b = find(a), find(b)
            if a == b:
                return
            if size[a] < size[b]:
                a, b = b, a
            parent[b] = a
            size[a] += size[b]
            least[a] = min(least[a], least[b])

        active_sparse = []
        incidence_count = 0
        for a, b, incidences in self.face_corner_equations:
            check()
            label = tuple((index[item], sign) for item, sign in incidences
                          if item in index)
            if label:
                active_sparse.append((a, b, label))
                incidence_count += len(label)
            else:
                union(a, b)

        corner_class = tuple(least[find(i)] for i in range(4*count))
        vertex_groups = {}
        for i, c in enumerate(corner_class):
            check()
            vertex_groups.setdefault(prepared['vertex_roots'][i], set()).add(c)
        groups = tuple(tuple(sorted(group))
                       for _, group in sorted(vertex_groups.items()) if len(group) > 1)
        classes = tuple(sorted(c for group in groups for c in group))
        class_index = {c: i for i, c in enumerate(classes)}
        adjacency = {c: [] for c in set(corner_class)}
        active = []
        matrix = []
        for a, b, sparse_label in active_sparse:
            check()
            label = [0]*k
            for j, value in sparse_label:
                label[j] = value
            label = tuple(label)
            a, b = corner_class[a], corner_class[b]
            active.append((a, b, label))
            adjacency[a].append((b, label))
            adjacency[b].append((a, tuple(-x for x in label)))
            row = [0]*(len(classes)+k)
            if a in class_index:
                row[class_index[a]] -= 1
            if b in class_index:
                row[class_index[b]] += 1
            for j, value in sparse_label:
                row[len(classes)+j] -= value
            if any(row):
                matrix.append(tuple(row))

        potentials = {}
        zero = (0,)*k
        for root in sorted(adjacency):
            if root in potentials:
                continue
            potentials[root] = zero
            queue = [root]
            for a in queue:
                check()
                for b, label in adjacency[a]:
                    if b not in potentials:
                        potentials[b] = tuple(x+y for x, y in zip(potentials[a], label))
                        queue.append(b)
        cycle_set = set()
        for a, b, label in active:
            check()
            row = _primitive(x+y-z for x, y, z
                             in zip(potentials[a], label, potentials[b]))
            if any(row):
                cycle_set.add(row)
        cycle_rows = _ordered_cycle_rows(cycle_set, k, check)
        basis = tuple(tuple(row) for row in _nullspace(cycle_rows, k, check))
        stats = dict(tetrahedra=count, allowed_types=k, active_equations=len(active),
                     triangle_classes=len(classes), kernel_variables=len(classes)+k,
                     kernel_equations=len(matrix), matching_nullity=len(basis),
                     matching_rank=k-len(basis),
                     removed_link_factors=sum(len(g) == 1 for g in vertex_groups.values()),
                     precompiled_equations=len(self.face_corner_equations),
                     sparse_label_incidences=incidence_count,
                     dense_labels_materialized=len(active),
                     dense_label_entries=k*len(active))
        if (len(active) > 4*k or incidence_count > 4*k or len(classes) > 8*k
                or any(sum(x*x for x in row) > 4 for row in matrix)):
            raise ArithmeticError('support-kernel size or row-norm invariant failed')
        return SectorKernel(self.triangulation, prepared, support, corner_class,
                            classes, groups, tuple(matrix), potentials, cycle_rows,
                            basis, stats)


def build_sparse_sector_kernel(triangulation, allowed_types, *, check=lambda: None):
    """Validate and build one sector; use ``PreparedSectorSource`` for reuse."""
    source = PreparedSectorSource(triangulation, check=check)
    return source.build(allowed_types, check=check)
