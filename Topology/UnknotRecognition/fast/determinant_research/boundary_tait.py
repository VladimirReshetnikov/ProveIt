"""Checked boundary-sized Tait quotient queries for a fixed classical suffix.

Research interface: report 26's exact rational terminal kernel supplies the
linear algebra. Cut-face fragments, rather than whole original regions, are
the common graph vertices. Query checks use only boundary identifications.
Production does not dispatch to this kernel until its setup cost is justified.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT/'fast'), str(ROOT/'reports/26')]
from fastunknot.diagram import DisjointSet
from fastunknot.boundary_connectivity import BoundaryConnectivity
from detshadow.diagram import Diagram as Ref
from detshadow.linalg import TerminalKernel, signed_laplacian, verify_kernel


def coloring(pd):
    diagram = Ref(tuple(pd))
    alpha = diagram.edge_involution()
    face, cycles = diagram.faces(alpha)
    color = [-1] * len(cycles)
    adjacent = [set() for _ in cycles]
    for d, a in enumerate(alpha):
        adjacent[face[d]].add(face[a])
    for start in range(len(cycles)):
        if color[start] >= 0:
            continue
        color[start] = 0
        queue = [start]
        for f in queue:
            for g in adjacent[f]:
                if color[g] < 0:
                    color[g] = 1-color[f]
                    queue.append(g)
                elif color[g] == color[f]:
                    raise ValueError('original faces are not checkerboard colorable')
    return tuple(color[f] for f in face)


class BoundaryTait:
    def __init__(self, pd, order, stage, palette=None, *, arithmetic='rational'):
        if arithmetic not in ('rational', 'integer'):
            raise ValueError('terminal arithmetic must be rational or integer')
        self.arithmetic = arithmetic
        if not 0 <= stage < len(order):
            raise ValueError('nonempty suffix required')
        palette = coloring(pd) if palette is None else palette
        self.n = len(order)-stage
        colors = [palette[4*i+j] for i in order[stage:] for j in range(4)]
        alpha, boundary = [-1]*(4*self.n), {}
        for k, i in enumerate(order[stage:]):
            for j, label in enumerate(pd[i]):
                dart = 4*k+j
                other = boundary.pop(label, None)
                if other is None:
                    boundary[label] = dart
                else:
                    alpha[dart], alpha[other] = other, dart
        self.labels = tuple(sorted(boundary))
        self.boundary = boundary
        self.connectivity = BoundaryConnectivity(alpha, boundary)
        faces, projection = DisjointSet(4*self.n), DisjointSet(self.n)
        rot = lambda d: (d & -4) | ((d+1) & 3)
        for d, a in enumerate(alpha):
            if a >= 0:
                faces.union(d, rot(a))
                projection.union(d//4, a//4)
        face_roots = {faces.find(d) for d in range(4*self.n)}
        face_colors = {}
        for d, c in enumerate(colors):
            f = faces.find(d)
            if f in face_colors and face_colors[f] != c:
                raise ValueError('cut face changes original color')
            face_colors[f] = c
        # Either shading is valid. Minimize the common graph before expensive
        # exact elimination; the phase below follows the selected shading.
        if sum(face_colors.values()) > len(face_colors)//2:
            colors = [1-c for c in colors]
            face_colors = {f: 1-c for f, c in face_colors.items()}
        ends = {label: faces.find(d) for label, d in boundary.items()}
        starts = {label: faces.find(rot(d)) for label, d in boundary.items()}
        open_faces = sorted(set(ends.values()) | set(starts.values()))
        face_ids = {f: i for i, f in enumerate(open_faces)}
        self.ends = {label: face_ids[f] for label, f in ends.items()}
        self.starts = {label: face_ids[f] for label, f in starts.items()}
        self.open_colors = tuple(face_colors[f] for f in open_faces)
        self.closed_faces = len(face_roots)-len(open_faces)
        black = sorted(f for f in face_roots if face_colors[f])
        black_ids = {f: i for i, f in enumerate(black)}
        terminal_faces = [f for f in open_faces if face_colors[f]]
        self.black_open = tuple(face_ids[f] for f in terminal_faces)
        self.closed_black = len(black)-len(terminal_faces)
        terminals = [black_ids[f] for f in terminal_faces]
        if not terminals:
            terminals = [0]  # no boundary: choose an artificial grounding vertex
        edges, self.B = [], 0
        for base in range(0, 4*self.n, 4):
            slots = [j for j in range(4) if colors[base+j]]
            if slots not in ([0, 2], [1, 3]):
                raise ValueError('invalid checkerboard sectors')
            u, v = [black_ids[faces.find(base+j)] for j in slots]
            b = int(slots == [0, 2])
            self.B += b
            edges.append((u, v, -1 if b else 1))
        self.laplacian = signed_laplacian(len(black), edges)
        roots = {projection.find(i) for i in range(self.n)}
        open_roots = sorted({projection.find(d//4) for d in boundary.values()})
        ids = {v: i for i, v in enumerate(open_roots)}
        self.projection = {label: ids[projection.find(d//4)] for label, d in boundary.items()}
        self.closed_projection = len(roots)-len(open_roots)
        self.projection_size = len(open_roots)
        self.terminals = tuple(terminals)
        self.kernel = None
        self.cache = {}

    def prepare_kernel(self, verify=False):
        if self.kernel is None:
            if self.arithmetic == 'integer':
                from fastunknot.terminal_determinant import IntegerTerminalKernel, verify_integer_terminal_kernel
                kernel = IntegerTerminalKernel.build(self.laplacian, self.terminals)
                valid = not verify or verify_integer_terminal_kernel(self.laplacian, kernel)
            else:
                kernel = TerminalKernel.build(self.laplacian, self.terminals)
                valid = not verify or verify_kernel(self.laplacian, kernel)
            if not valid:
                raise ArithmeticError('terminal kernel certificate failed')
            self.kernel = kernel

    def partition(self, pairs):
        """Verify the completion and return its partition, phase and counts.

        Work is O(boundary size), apart from union-find factors. Closed face
        fragments and projection components are counted in constant time.
        Color-incompatible pairings decline; positive-genus pairings reject.
        """
        pairs = tuple(pairs)
        # Coverage validation and both circle counts use only boundary paths.
        components, zero = self.connectivity.counts(pairs)
        faces = DisjointSet(len(self.open_colors))
        projection = DisjointSet(self.projection_size)
        for a, b in pairs:
            for end, start in ((self.ends[a], self.starts[b]),
                               (self.ends[b], self.starts[a])):
                if self.open_colors[end] != self.open_colors[start]:
                    raise ValueError('matching is incompatible with inherited face colors')
                faces.union(end, start)
            projection.union(self.projection[a], self.projection[b])
        shadows = self.closed_projection + len({projection.find(i) for i in range(self.projection_size)})
        face_count = self.closed_faces + len({faces.find(i) for i in range(len(self.open_colors))})
        if face_count != self.n + 2*shadows:
            raise ValueError('matching completion is not spherical')
        labels = tuple(faces.find(i) for i in self.black_open) or (0,)
        vertices = self.closed_black + len({faces.find(i) for i in self.black_open})
        return dict(partition=labels, phase=(self.B+vertices-1) % 4,
                    black_vertices=vertices, shadow_components=shadows,
                    link_components=components, zero_circles=zero,
                    unreduced_euler=(-1 if (self.n+components+zero) % 2 else 1)*(1 << components))

    def evaluate(self, pairs):
        data = self.partition(pairs)
        if data['shadow_components'] != 1:
            return (0, 0), data
        self.prepare_kernel()
        names = {}
        key = tuple(names.setdefault(v, len(names)) for v in data['partition'])
        if key not in self.cache:
            self.cache[key] = self.kernel.query(key)
        value = self.cache[key]
        unit = ((1, 0), (0, -1), (-1, 0), (0, 1))[data['phase']]
        return (unit[0]*value, unit[1]*value), data
