"""Independent DSU reblocking and original-edge address verification.

No functions from stable.py are imported. The existing independent aligned
checker verifies the nested graph certificate and compressed coloring.
"""

from pattern_kernel.core import Block, Tile, source_digest, validate_chain

from .verify import analyse, require
from .verify import verify_result as aligned_verify_result
from .verify import verify_source_witness as aligned_verify_source_witness


def _equal(left, right):
    """Typed equality: booleans cannot masquerade as metadata integers."""
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(_equal(left[k], right[k]) for k in left)
    if type(left) is list:
        return len(left) == len(right) and all(_equal(a, b) for a, b in zip(left, right))
    return left == right


def _through_rank(tile):
    parent = list(range(tile.n))
    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v
    for a, b in tile.edges:
        a, b = root(a), root(b)
        if a != b:
            parent[max(a, b)] = min(a, b)
    all_roots = {root(v) for v in range(tile.n)}
    left = {root(v) for v in tile.left}
    right = {root(v) for v in tile.right}
    require(all_roots == left == right, 'a component misses an interface')
    return len(all_roots)


def _stack(tile, count, bound):
    require(type(count) is int and 1 <= count <= bound, 'unbounded explicit stack')
    parent = list(range(count * tile.n))
    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    for phase in range(1, count):
        for outgoing, incoming in zip(tile.right, tile.left):
            a = root((phase - 1) * tile.n + outgoing)
            b = root(phase * tile.n + incoming)
            if a != b:
                parent[max(a, b)] = min(a, b)
    names, image = {}, []
    for v in range(len(parent)):
        rep = root(v)
        if rep not in names:
            names[rep] = len(names)
        image.append(names[rep])
    edges = tuple((image[phase * tile.n + a], image[phase * tile.n + b])
                  for phase in range(count) for a, b in tile.edges)
    return Tile(len(names), edges, tuple(image[v] for v in tile.left),
                tuple(image[(count - 1) * tile.n + v] for v in tile.right))


def reconstruct(chain, plans):
    """Independently reconstruct bounded powers and their original edge charts."""
    validate_chain(chain, cubic=False)
    require(type(plans) is list and len(plans) == len(chain), 'wrong reblocking plan count')
    adapted, charts = [], []
    for bi, (block, plan) in enumerate(zip(chain, plans)):
        require(type(block.copies) is int, 'exact source exponent required')
        tile, exponent = block.tile, block.copies
        try:
            d = _through_rank(tile)
        except ValueError:
            require(exponent <= 4, 'large non-through block is unsupported')
            expected = dict(kind='literal', copies=exponent, adapted_blocks=[len(adapted)])
            require(_equal(plan, expected), 'invalid literal reblocking metadata')
            adapted.append(block)
            charts.append(dict(block=bi, phases=1, offset=0, copies=exponent,
                               local_edges=len(tile.edges)))
            continue
        require(type(plan) is dict and plan.get('kind') == 'through', 'missing through plan')
        period = plan.get('period')
        require(type(period) is int and 1 <= period <= d, 'period exceeds component bound')
        ranks, full = [], None
        for count in range(1, period + 1):
            candidate = _stack(tile, count, d)
            ranks.append(_through_rank(candidate))
            try:
                analyse(candidate)
                aligned = True
            except ValueError:
                aligned = False
            require(aligned == (count == period), 'period is not the least aligned power')
            full = candidate
        quotient, remainder = divmod(exponent, period)
        indices = []
        if quotient:
            indices.append(len(adapted))
            adapted.append(Block(full, quotient))
            charts.append(dict(block=bi, phases=period, offset=0, copies=quotient,
                               local_edges=len(tile.edges)))
        if remainder:
            indices.append(len(adapted))
            adapted.append(Block(_stack(tile, remainder, d), 1))
            charts.append(dict(block=bi, phases=remainder, offset=period * quotient,
                               copies=1, local_edges=len(tile.edges)))
        expected = dict(kind='through', components=d, period=period, ranks=ranks,
                        quotient=hex(quotient), remainder=remainder,
                        adapted_blocks=indices)
        require(_equal(plan, expected), 'reblocking metadata differs from original source')
    adapted = tuple(adapted)
    validate_chain(adapted, cubic=False)
    return adapted, charts


def _original_addresses(chain, adapted, charts, nested):
    source = aligned_verify_source_witness(adapted, nested['source_witness'])
    def convert(item):
        require(type(item['block']) is int and 0 <= item['block'] < len(charts),
                'invalid adapted block address')
        chart = charts[item['block']]
        require(type(item['edge']) is int and 0 <= item['edge'] <
                chart['phases'] * chart['local_edges'], 'invalid adapted edge occurrence')
        phase, edge = divmod(item['edge'], chart['local_edges'])
        value = item['copy']
        require(type(value) is str and value.startswith('0x'), 'hexadecimal copy address required')
        copy = int(value, 16)
        require(0 <= copy < chart['copies'], 'adapted copy out of range')
        original = chart['offset'] + chart['phases'] * copy + phase
        require(0 <= original < chain[chart['block']].copies, 'original copy out of range')
        return dict(block=chart['block'], copy=hex(original), edge=edge)
    result = dict(cost=source['cost'], crossings=[convert(e) for e in source['crossings']],
                  anchors=[convert(e) for e in source['anchors']])
    require(len(result['crossings']) == result['cost'] <= 3, 'original cut cost changed')
    require(len({(x['block'], x['copy'], x['edge']) for x in result['crossings']})
            == result['cost'], 'original edge occurrence duplicated')
    return result


def verify_source_witness(chain, result):
    """Check a wrapper result's compressed coloring and original edge addresses.

    This returns the source cost, crossings, and two anchors, or rejects the input.
    Use verify_result when the nested graph verdict must also be authenticated.
    """
    validate_chain(chain)
    require(type(result) is dict, 'wrapper result must be a dictionary')
    require(result.get('schema') == 'stable-routed-cubic-cut-v1', 'wrong wrapper schema')
    require(result.get('verdict') == 'LOW_CYCLIC_CUT', 'no negative source coloring')
    require(result.get('source_sha256') == source_digest(chain), 'original source mismatch')
    adapted, charts = reconstruct(chain, result['reblocking'])
    require(result.get('adapted_sha256') == source_digest(adapted), 'adapted source mismatch')
    source = _original_addresses(chain, adapted, charts, result['nested'])
    require(_equal(result.get('original_source_addresses'), source), 'original source lift differs')
    return source


def verify_result(chain, result):
    """Verify exact reblocking, nested routed certificate, and original-source lift."""
    try:
        validate_chain(chain)
        require(type(result) is dict, 'wrapper result must be a dictionary')
        fields = {'schema', 'source_sha256', 'reblocking', 'adapted_sha256', 'verdict', 'nested'}
        verdict = result.get('verdict')
        if verdict == 'LOW_CYCLIC_CUT':
            fields.add('original_source_addresses')
        require(set(result) == fields, 'invalid wrapper fields')
        require(result['schema'] == 'stable-routed-cubic-cut-v1', 'wrong wrapper schema')
        require(result['source_sha256'] == source_digest(chain), 'original source mismatch')
        adapted, charts = reconstruct(chain, result['reblocking'])
        require(result['adapted_sha256'] == source_digest(adapted), 'adapted source mismatch')
        validate_chain(adapted)
        require(aligned_verify_result(adapted, result['nested']), 'nested routing proof failed')
        require(verdict == result['nested']['graph_proof']['verdict'], 'graph verdict differs')
        if verdict == 'LOW_CYCLIC_CUT':
            source = _original_addresses(chain, adapted, charts, result['nested'])
            require(_equal(result['original_source_addresses'], source), 'original lift differs')
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False
