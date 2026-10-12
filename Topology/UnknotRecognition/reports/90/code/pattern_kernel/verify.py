"""Proof replay without invoking kernel production or max-flow search.

Local type/degree checks and the immutable input model are shared. The checker
independently assembles fresh-copy quotients and checks residual augmentations.
"""
from __future__ import annotations
from .core import Block, Graph, source_digest, validate_chain


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _integer(x: object) -> bool:
    return type(x) is int


def _hex(x: object, *, positive: bool = False) -> int:
    _require(isinstance(x, str) and x.startswith('0x'), 'hexadecimal string required')
    v = int(x, 16)
    _require(v >= (1 if positive else 0), 'invalid hexadecimal integer')
    return v


def _assemble(chain: tuple[Block, ...], counts: list[int]) -> Graph:
    """Fresh-copy DSU oracle (not the producer's incremental shared-vertex map)."""
    parent: list[int] = []; all_edges = []; copies = []
    def root(x: int) -> int:
        while parent[x] != x:
            x = parent[x]
        return x
    def join(a: int, b: int) -> None:
        a, b = root(a), root(b)
        if a != b:
            parent[max(a, b)] = min(a, b)
    for block, count in zip(chain, counts):
        t = block.tile
        for _ in range(count):
            offset = len(parent); parent.extend(range(offset, offset + t.n))
            copies.append((t, offset))
            all_edges.extend((a + offset, b + offset) for a, b in t.edges)
    for (a, oa), (b, ob) in zip(copies, copies[1:] + copies[:1]):
        for x, y in zip(a.right, b.left):
            join(x + oa, y + ob)
    labels = {}; image = []
    for v in range(len(parent)):
        rv = root(v)
        if rv not in labels:
            labels[rv] = len(labels)
        image.append(labels[rv])
    return Graph(len(labels), tuple((image[a], image[b]) for a, b in all_edges))


def _connected(tile) -> bool:
    # Independent union-find rather than the producer's adjacency traversal.
    p = list(range(tile.n))
    def root(x: int) -> int:
        while p[x] != x:
            x = p[x]
        return x
    for a, b in tile.edges:
        a, b = root(a), root(b)
        p[b] = a
    return len({root(x) for x in range(tile.n)}) == 1


def _check_graph(g: Graph, proof: dict) -> None:
    _require(g.cubic(), 'kernel is not cubic')
    if proof.get('verdict') == 'LOW_CYCLIC_CUT':
        shore = proof.get('shore')
        _require(isinstance(shore, list) and all(_integer(v) and 0 <= v < g.n
                                               for v in shore), 'bad shore')
        _require(len(set(shore)) == len(shore), 'duplicate shore vertex')
        side = set(shore); flags = 0; cut = []
        for i, (a, b) in enumerate(g.edges):
            if (a in side) != (b in side):
                cut.append(i)
            else:
                flags |= 2 if a in side else 1
        _require(flags == 3 and len(cut) <= 3, 'not a marked small cut')
        _require(proof.get('cut_edges') == cut and proof.get('cost') == len(cut),
                 'cut metadata mismatch')
        return
    _require(proof.get('verdict') == 'NO_LOW_CYCLIC_CUT', 'bad verdict')
    records = proof.get('four_flows')
    _require(isinstance(records, list), 'missing flow certificates')
    expected = [(e, f) for e in range(len(g.edges)) for f in range(e + 1, len(g.edges))
                if not (set(g.edges[e]) & set(g.edges[f]))]
    _require(len(records) == len(expected), 'missing/extra anchor pair')
    for record, (e, f) in zip(records, expected):
        _require(record.get('anchors') == [e, f], 'anchor order mismatch')
        n = g.n + 2; source, sink = g.n, g.n + 1
        # Dense capacities are deliberately different from sparse producer state.
        cap = [[0] * n for _ in range(n)]
        for a, b in g.edges:
            if a != b:
                cap[a][b] += 1; cap[b][a] += 1
        for a in set(g.edges[e]):
            cap[source][a] = 4
        for b in set(g.edges[f]):
            cap[b][sink] = 4
        value = 0
        steps = record.get('augmentations')
        _require(isinstance(steps, list) and len(steps) <= 4, 'bad augmentation count')
        for step in steps:
            path, amount = step.get('path'), step.get('amount')
            _require(isinstance(path, list) and 2 <= len(path) <= n,
                     'bad augmenting path length')
            _require(all(_integer(v) and 0 <= v < n for v in path)
                     and len(set(path)) == len(path), 'bad augmenting path vertices')
            _require(path[0] == source and path[-1] == sink, 'bad endpoints')
            _require(_integer(amount) and 1 <= amount <= 4 - value, 'bad flow amount')
            for a, b in zip(path, path[1:]):
                _require(cap[a][b] >= amount, 'residual capacity violated')
                cap[a][b] -= amount; cap[b][a] += amount
            value += amount
        _require(value == 4, 'flow does not exclude cuts at most three')


def verify_source_witness(chain: tuple[Block, ...], witness: dict) -> dict:
    """Check a succinct ORIGINAL coloring and return <=3 original edge addresses.

    Raises ValueError for malformed proofs. No huge multiplicity is expanded.
    Addresses have zero-based block/copy/edge coordinates; copy indices are hex.
    """
    validate_chain(chain)
    _require(witness.get('schema') == 'source-cut-coloring-v1', 'wrong schema')
    _require(witness.get('source_sha256') == source_digest(chain), 'source mismatch')
    blocks = witness.get('blocks')
    _require(isinstance(blocks, list) and len(blocks) == len(chain), 'bad blocks')
    first = None; last = None; cost = 0; flags = 0; crossings = []; anchors = {}
    for bi, (block, runs) in enumerate(zip(chain, blocks)):
        t = block.tile; offset = 0
        _require(isinstance(runs, list) and 1 <= len(runs) <= 4, 'bad run count')
        for run in runs:
            mask = _hex(run.get('colors')); repeat = _hex(run.get('copies'), positive=True)
            _require(mask < 1 << t.n, 'local color outside vertex range')
            left = tuple((mask >> v) & 1 for v in t.left)
            right = tuple((mask >> v) & 1 for v in t.right)
            if first is None:
                first = left
            if last is not None:
                _require(last == left, 'color disagreement at a seam')
            if repeat > 1:
                _require(left == right, 'color disagreement in a repeated run')
            mixed = []
            for ei, (a, b) in enumerate(t.edges):
                ca, cb = (mask >> a) & 1, (mask >> b) & 1
                if ca != cb:
                    mixed.append(ei)
                else:
                    flags |= 1 << ca
                    anchors.setdefault(ca, {'block': bi, 'copy': hex(offset), 'edge': ei})
            cost += repeat * len(mixed)
            _require(cost <= 3, 'too many cut edges')
            if mixed:
                # The preceding check proves repeat <=3; this is never a huge loop.
                for j in range(repeat):
                    crossings.extend({'block': bi, 'copy': hex(offset + j), 'edge': e}
                                     for e in mixed)
            offset += repeat; last = right
        _require(offset == block.copies, 'source multiplicity mismatch')
    _require(last == first, 'closure colors disagree')
    _require(flags == 3, 'both monochromatic edge witnesses are required')
    return {'cost': cost, 'crossings': crossings,
            'anchors': [anchors[0], anchors[1]]}


def verify_result(chain: tuple[Block, ...], result: dict) -> bool:
    """Return false on malformed proof data; never invoke proof search."""
    try:
        validate_chain(chain)
        _require(result.get('schema') == 'compressed-cubic-cut-v1', 'wrong result schema')
        reduction = result['reduction']
        _require(reduction.get('schema') == 'four-copy-reduction-v1', 'wrong reduction schema')
        _require(reduction.get('source_sha256') == source_digest(chain), 'source mismatch')
        _require(type(reduction.get('threshold')) is int and reduction['threshold'] == 3,
                 'bad threshold')
        _require(reduction.get('source_copies') == [hex(b.copies) for b in chain],
                 'bad source counts')
        counts = reduction.get('kernel_copies')
        _require(isinstance(counts, list) and len(counts) == len(chain), 'bad kernel counts')
        for block, count in zip(chain, counts):
            _require(_integer(count) and count == min(block.copies, 4), 'invalid cap')
            if count < block.copies:
                _require(_connected(block.tile), 'disconnected capped tile')
        g = _assemble(chain, counts)
        _require(result.get('kernel') == {'n': g.n, 'edges': [list(e) for e in g.edges]},
                 'kernel does not reconstruct from source')
        _check_graph(g, result['graph_proof'])
        if result['graph_proof']['verdict'] == 'LOW_CYCLIC_CUT':
            verify_source_witness(chain, result['source_witness'])
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False
