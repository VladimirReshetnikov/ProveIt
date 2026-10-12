"""Polynomial reblocking for arbitrary through-component tile powers.

The original chain is rebracketed exactly before the existing aligned routing
kernel is invoked. Every component must meet both interfaces; small unsupported
blocks may instead be retained literally. This module makes graph verdicts only.
"""

from pattern_kernel.core import Block, Tile, source_digest, validate_chain

from .core import build_kernel as aligned_build_kernel
from .core import components as aligned_components
from .core import connected_cutoff
from .core import solve as aligned_solve
from .verify import verify_source_witness as aligned_source_witness


class UnsupportedTile(ValueError):
    """A large block has a component missing an interface."""


def through_components(tile):
    """Return connected components without requiring partition alignment."""
    adjacency = [[] for _ in range(tile.n)]
    for a, b in tile.edges:
        adjacency[a].append(b)
        adjacency[b].append(a)
    unseen, records = set(range(tile.n)), []
    while unseen:
        seed = min(unseen)
        unseen.remove(seed)
        vertices, todo = {seed}, [seed]
        while todo:
            for v in adjacency[todo.pop()]:
                if v in unseen:
                    unseen.remove(v)
                    vertices.add(v)
                    todo.append(v)
        left = tuple(i for i, v in enumerate(tile.left) if v in vertices)
        right = tuple(i for i, v in enumerate(tile.right) if v in vertices)
        if not left or not right:
            raise UnsupportedTile('every component must meet both interfaces')
        records.append(dict(vertices=sorted(vertices), left=left, right=right))
    return sorted(records, key=lambda item: item['left'])


def _power_tile(tile, count):
    """Exact bounded open stacking, retaining edge order (phase, local edge)."""
    if type(count) is not int or count < 1:
        raise ValueError('a positive bounded stacking count is required')
    if count == 1:
        return tile
    edges, vertex_count, first, previous = [], 0, None, None
    for _ in range(count):
        image = {}
        if previous is not None:
            image.update(zip(tile.left, previous))
        for local in range(tile.n):
            if local not in image:
                image[local] = vertex_count
                vertex_count += 1
        if first is None:
            first = tuple(image[v] for v in tile.left)
        previous = tuple(image[v] for v in tile.right)
        edges.extend((image[a], image[b]) for a, b in tile.edges)
    return Tile(vertex_count, tuple(edges), first, previous)


def reblock_chain(chain, *, literal_limit=4):
    """Return exact adapted blocks, bounded metadata and edge-address charts.

    The least aligned power is found among at most d original copies, where d
    is the original component count. No loop uses a binary exponent as a bound.
    Tail powers are each retained as one explicit tile with multiplicity one.
    """
    validate_chain(chain, cubic=False)
    if type(literal_limit) is not int or literal_limit < 0:
        raise ValueError('invalid literal fallback limit')
    adapted, plans, charts = [], [], []
    for block_index, block in enumerate(chain):
        if type(block.copies) is not int:
            raise ValueError('Block copies must be an exact integer')
        tile, exponent = block.tile, block.copies
        try:
            d = len(through_components(tile))
        except UnsupportedTile:
            if exponent > literal_limit:
                raise UnsupportedTile('large block has a component missing an interface')
            index = len(adapted)
            adapted.append(block)
            plans.append(dict(kind='literal', copies=exponent, adapted_blocks=[index]))
            charts.append(dict(block=block_index, phases=1, offset=0,
                               copies=exponent, local_edges=len(tile.edges)))
            continue
        ranks = []
        for period in range(1, d + 1):
            full = _power_tile(tile, period)
            ranks.append(len(through_components(full)))
            try:
                aligned_components(full)
                break
            except ValueError:
                pass
        else:
            raise ArithmeticError('through-component stabilization bound failed')
        quotient, remainder = divmod(exponent, period)
        indices = []
        if quotient:
            indices.append(len(adapted))
            adapted.append(Block(full, quotient))
            charts.append(dict(block=block_index, phases=period, offset=0,
                               copies=quotient, local_edges=len(tile.edges)))
        if remainder:
            indices.append(len(adapted))
            adapted.append(Block(_power_tile(tile, remainder), 1))
            charts.append(dict(block=block_index, phases=remainder,
                               offset=period * quotient, copies=1,
                               local_edges=len(tile.edges)))
        plans.append(dict(kind='through', components=d, period=period, ranks=ranks,
                          quotient=hex(quotient), remainder=remainder,
                          adapted_blocks=indices))
    adapted = tuple(adapted)
    validate_chain(adapted, cubic=False)
    return adapted, plans, charts


def build_kernel(chain, threshold=3, *, close=True):
    """Open or closed graph kernel after exact through-component reblocking."""
    if type(threshold) is not int or threshold < 0:
        raise ValueError('nonnegative integer threshold required')
    limit = connected_cutoff(threshold)
    adapted, plans, _ = reblock_chain(chain, literal_limit=limit)
    graph, routing, views = aligned_build_kernel(adapted, threshold, close=close)
    return graph, dict(reblocking=plans, routing=routing,
                      adapted_sha256=source_digest(adapted)), views


def _map_source_addresses(source, charts):
    def address(item):
        chart = charts[item['block']]
        phase, local_edge = divmod(item['edge'], chart['local_edges'])
        adapted_copy = int(item['copy'], 16)
        if not 0 <= phase < chart['phases'] or not 0 <= adapted_copy < chart['copies']:
            raise ArithmeticError('invalid adapted source edge address')
        original_copy = chart['offset'] + chart['phases'] * adapted_copy + phase
        return dict(block=chart['block'], copy=hex(original_copy), edge=local_edge)
    return dict(cost=source['cost'], crossings=[address(e) for e in source['crossings']],
                anchors=[address(e) for e in source['anchors']])


def solve(chain):
    """Certified cubic graph predicate for through-component flat chains."""
    validate_chain(chain)
    adapted, plans, charts = reblock_chain(chain)
    validate_chain(adapted)
    nested = aligned_solve(adapted)
    result = dict(schema='stable-routed-cubic-cut-v1', source_sha256=source_digest(chain),
                  reblocking=plans, adapted_sha256=source_digest(adapted),
                  verdict=nested['graph_proof']['verdict'], nested=nested)
    if result['verdict'] == 'LOW_CYCLIC_CUT':
        source = aligned_source_witness(adapted, nested['source_witness'])
        result['original_source_addresses'] = _map_source_addresses(source, charts)
    return result
