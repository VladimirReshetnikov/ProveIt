"""Four-copy kernels for unit-edge cuts of cubic graph-pattern grammars.

This module decides a graph predicate, NOT whether a 3-manifold is a ball
and NOT whether a knot is unknotted. Sphere/ball geometry is external.
Python >=3.10; standard library only. Parallel edges and loops are retained.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import deque
from hashlib import sha256
import json
from typing import Iterable


def natural(x: object) -> int:
    """Accept positive integers or hexadecimal strings; reject booleans."""
    if type(x) is int:
        value = x
    elif isinstance(x, str) and x.startswith('0x'):
        value = int(x, 16)
    else:
        raise ValueError('expected a positive integer or 0x-prefixed string')
    if value < 1:
        raise ValueError('copy counts must be positive')
    return value


@dataclass(frozen=True)
class Tile:
    n: int
    edges: tuple[tuple[int, int], ...]
    left: tuple[int, ...]
    right: tuple[int, ...]

    def __post_init__(self) -> None:
        if type(self.n) is not int or self.n < 2:
            raise ValueError('tile vertex count must be at least two')
        ports = self.left + self.right
        if not self.left or len(self.left) != len(self.right):
            raise ValueError('nonempty equal-width interfaces required')
        if len(set(ports)) != len(ports):
            raise ValueError('interfaces must be injective and disjoint')
        if any(type(v) is not int or not 0 <= v < self.n for v in ports):
            raise ValueError('invalid port')
        if any(len(e) != 2 or any(type(v) is not int or not 0 <= v < self.n
                                 for v in e) for e in self.edges):
            raise ValueError('invalid edge')

    @property
    def width(self) -> int:
        return len(self.left)

    def degrees(self) -> list[int]:
        d = [0] * self.n
        for a, b in self.edges:
            d[a] += 1; d[b] += 1  # a loop contributes two
        return d

    def connected(self) -> bool:
        adj = [[] for _ in range(self.n)]
        for a, b in self.edges:
            adj[a].append(b); adj[b].append(a)
        seen = {0}; stack = [0]
        while stack:
            for v in adj[stack.pop()]:
                if v not in seen:
                    seen.add(v); stack.append(v)
        return len(seen) == self.n

    def payload(self) -> dict:
        return {'n': self.n, 'edges': [list(e) for e in self.edges],
                'left': list(self.left), 'right': list(self.right)}


@dataclass(frozen=True)
class Block:
    tile: Tile
    copies: int

    def __post_init__(self) -> None:
        natural(self.copies)


@dataclass(frozen=True)
class Graph:
    n: int
    edges: tuple[tuple[int, int], ...]

    def cubic(self) -> bool:
        degrees = [0] * self.n
        for a, b in self.edges:
            degrees[a] += 1; degrees[b] += 1
        return bool(degrees) and all(d == 3 for d in degrees)


def chain_payload(chain: tuple[Block, ...]) -> dict:
    return {'schema': 'closed-tile-chain-v1', 'blocks': [
        {'tile': b.tile.payload(), 'copies': hex(b.copies)} for b in chain]}


def source_digest(chain: tuple[Block, ...]) -> str:
    raw = json.dumps(chain_payload(chain), sort_keys=True,
                     separators=(',', ':')).encode('ascii')
    return sha256(raw).hexdigest()


def validate_chain(chain: tuple[Block, ...], *, cubic: bool = True) -> None:
    if not chain:
        raise ValueError('a nonempty chain is required')
    width = chain[0].tile.width
    for block in chain:
        natural(block.copies)
        t = block.tile
        if t.width != width:
            raise ValueError('interface widths disagree')
        if cubic:
            d = t.degrees(); boundary = set(t.left + t.right)
            if any(d[v] != 3 for v in range(t.n) if v not in boundary):
                raise ValueError('a private vertex is not cubic')
            if block.copies > 1 and any(d[a] + d[b] != 3
                                       for a, b in zip(t.right, t.left)):
                raise ValueError('a repeated seam is not cubic')
    if cubic:
        for a, b in zip(chain, chain[1:] + chain[:1]):
            da, db = a.tile.degrees(), b.tile.degrees()
            if any(da[u] + db[v] != 3
                   for u, v in zip(a.tile.right, b.tile.left)):
                raise ValueError('a block/closure seam is not cubic')


class DSU:
    def __init__(self, n: int):
        self.p = list(range(n))
    def find(self, x: int) -> int:
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]; x = self.p[x]
        return x
    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a != b:
            self.p[b] = a


def expand(chain: tuple[Block, ...], *, max_copies: int = 100000
           ) -> tuple[Graph, list[list[list[int]]]]:
    """Explicit reference/finite kernel assembly; a hard cap prevents expansion.

    Returns vertex maps indexed by block, copy, local vertex. The maps support
    lifting a finite-kernel coloring to a succinct original-source coloring.
    """
    validate_chain(chain, cubic=False)
    if sum(b.copies for b in chain) > max_copies:
        raise ValueError('explicit expansion cap exceeded')
    edges = []; maps = []; count = 0; previous = None; first = None
    for block in chain:
        t = block.tile; block_maps = []
        for _ in range(block.copies):
            image = [-1] * t.n
            if previous is not None:
                for local, global_v in zip(t.left, previous):
                    image[local] = global_v
            for local in range(t.n):
                if image[local] == -1:
                    image[local] = count; count += 1
            if first is None:
                first = [image[v] for v in t.left]
            previous = [image[v] for v in t.right]
            edges.extend((image[u], image[v]) for u, v in t.edges)
            block_maps.append(image)
        maps.append(block_maps)
    dsu = DSU(count)
    for a, b in zip(previous, first):
        dsu.union(a, b)
    names = {}; convert = []
    for v in range(count):
        root = dsu.find(v)
        if root not in names:
            names[root] = len(names)
        convert.append(names[root])
    graph = Graph(len(names), tuple((convert[a], convert[b]) for a, b in edges))
    final_maps = [[[convert[v] for v in image] for image in block] for block in maps]
    return graph, final_maps


def kernelize(chain: tuple[Block, ...], *, threshold: int = 3
              ) -> tuple[tuple[Block, ...], dict]:
    """Exact marked-cut reduction. Only threshold three has cubic topology scope."""
    if type(threshold) is not int or threshold < 0:
        raise ValueError('invalid threshold')
    validate_chain(chain, cubic=False)
    limit = 4 if threshold == 3 else threshold + 2
    reduced = []
    for b in chain:
        if b.copies > limit and not b.tile.connected():
            raise ValueError('cannot cap a disconnected tile')
        reduced.append(Block(b.tile, min(b.copies, limit)))
    certificate = {'schema': 'four-copy-reduction-v1',
                   'source_sha256': source_digest(chain),
                   'threshold': threshold,
                   'source_copies': [hex(b.copies) for b in chain],
                   'kernel_copies': [b.copies for b in reduced]}
    return tuple(reduced), certificate


def _network(g: Graph, e: int, f: int, cap: int) -> list[dict[int, int]]:
    source, sink = g.n, g.n + 1
    residual: list[dict[int, int]] = [{} for _ in range(g.n + 2)]
    def add(a: int, b: int, c: int) -> None:
        residual[a][b] = residual[a].get(b, 0) + c
        residual[b].setdefault(a, 0)
    for a, b in g.edges:
        if a != b:
            add(a, b, 1); add(b, a, 1)
    for a in set(g.edges[e]):
        add(source, a, cap)
    for b in set(g.edges[f]):
        add(b, sink, cap)
    return residual


def _flow(g: Graph, e: int, f: int, cap: int = 4
          ) -> tuple[int, list[int], list[dict]]:
    residual = _network(g, e, f, cap)
    source, sink = g.n, g.n + 1
    value = 0; steps = []
    while value < cap:
        parent = [-1] * len(residual); parent[source] = source
        q = deque([source])
        while q and parent[sink] == -1:
            u = q.popleft()
            for v, c in residual[u].items():
                if c > 0 and parent[v] == -1:
                    parent[v] = u; q.append(v)
        if parent[sink] == -1:
            return value, [v for v in range(g.n) if parent[v] != -1], steps
        path = [sink]
        while path[-1] != source:
            path.append(parent[path[-1]])
        path.reverse()
        delta = min(cap - value, *(residual[u][v] for u, v in zip(path, path[1:])))
        for u, v in zip(path, path[1:]):
            residual[u][v] -= delta
            residual[v][u] = residual[v].get(u, 0) + delta
        steps.append({'path': path, 'amount': delta}); value += delta
    return value, [], steps


def certify_cubic_graph(g: Graph) -> dict:
    """Return a small cyclic cut, or a complete four-flow certificate.

    No planarity assertion is made. For a supplied spherical boundary pattern
    in a certified ball, NO_LOW_CYCLIC_CUT is exactly essentiality.
    """
    if not g.cubic():
        raise ValueError('the graph is not cubic')
    flows = []
    for e in range(len(g.edges)):
        for f in range(e + 1, len(g.edges)):
            if set(g.edges[e]) & set(g.edges[f]):
                continue
            value, shore, steps = _flow(g, e, f)
            if value <= 3:
                selected = set(shore)
                cuts = [i for i, (a, b) in enumerate(g.edges)
                        if (a in selected) != (b in selected)]
                return {'verdict': 'LOW_CYCLIC_CUT', 'shore': shore,
                        'anchors': [e, f], 'cut_edges': cuts, 'cost': len(cuts)}
            flows.append({'anchors': [e, f], 'augmentations': steps})
    return {'verdict': 'NO_LOW_CYCLIC_CUT', 'four_flows': flows}


def solve(chain: tuple[Block, ...]) -> dict:
    validate_chain(chain)
    reduced, reduction = kernelize(chain)
    graph, maps = expand(reduced)
    proof = certify_cubic_graph(graph)
    result = {'schema': 'compressed-cubic-cut-v1', 'reduction': reduction,
              'kernel': {'n': graph.n, 'edges': [list(e) for e in graph.edges]},
              'graph_proof': proof}
    if proof['verdict'] == 'LOW_CYCLIC_CUT':
        result['source_witness'] = lift_witness(chain, reduced, maps, proof['shore'])
    return result


def lift_witness(chain: tuple[Block, ...], reduced: tuple[Block, ...],
                 maps: list[list[list[int]]], shore: Iterable[int]) -> dict:
    selected = set(shore); blocks = []
    for original, short, images in zip(chain, reduced, maps):
        masks = [sum((int(v in selected) << local)
                     for local, v in enumerate(image)) for image in images]
        repeats = [1] * len(masks)
        if original.copies > short.copies:
            # A cut of cost at most three in four connected copies has a monochromatic copy.
            monochromatic = next((i for i, m in enumerate(masks)
                                  if m in (0, (1 << original.tile.n) - 1)), None)
            if monochromatic is None:
                raise ValueError('a required monochromatic copy is absent')
            repeats[monochromatic] += original.copies - short.copies
        blocks.append([{'colors': hex(m), 'copies': hex(r)}
                       for m, r in zip(masks, repeats)])
    return {'schema': 'source-cut-coloring-v1',
            'source_sha256': source_digest(chain), 'blocks': blocks}


def prism_tile() -> Tile:
    return Tile(4, ((0, 2), (1, 3), (2, 3)), (0, 1), (2, 3))


def triangle_expansion_tile() -> Tile:
    # Replace the output top vertex of the prism tile by a triangle (2,4,5).
    return Tile(6, ((0, 4), (1, 3), (3, 5), (2, 4), (4, 5), (5, 2)),
                (0, 1), (2, 3))
