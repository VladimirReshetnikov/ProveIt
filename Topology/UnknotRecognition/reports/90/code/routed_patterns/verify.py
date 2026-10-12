"""Independent finite reconstruction and compressed source-coloring replay.

This checker does not import the routing planner, producer, or witness lift.
It shares immutable types and the incoming independent graph-flow checker.
"""
from pattern_kernel.core import Graph, source_digest, validate_chain
from pattern_kernel.verify import _check_graph


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer_hex(value):
    require(isinstance(value, str) and value.startswith('0x'), 'hex integer required')
    result = int(value, 16)
    require(result >= 0, 'negative value')
    return result


def analyse(tile):
    """Use edge equivalence classes, independently of producer traversal."""
    parent = list(range(tile.n))
    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v
    for a, b in tile.edges:
        a, b = root(a), root(b)
        if a != b:
            parent[max(a, b)] = min(a, b)
    groups = {}
    for v in range(tile.n):
        groups.setdefault(root(v), []).append(v)
    records = []
    for vertices in groups.values():
        vs = set(vertices)
        left = tuple(i for i, v in enumerate(tile.left) if v in vs)
        right = tuple(i for i, v in enumerate(tile.right) if v in vs)
        require(left and right, 'a component misses an interface')
        records.append({'vertices': vertices, 'left': left, 'right': right,
                        'edges': [e for e, (a, _) in enumerate(tile.edges) if a in vs]})
    records.sort(key=lambda r: r['left'])
    parts = [r['left'] for r in records]
    require(set(parts) == {r['right'] for r in records}, 'unaligned partitions')
    permutation = [parts.index(r['right']) for r in records]
    return records, permutation


def orbit(permutation, start):
    result = []
    node = start
    while node not in result:
        result.append(node)
        node = permutation[node]
    require(node == start, 'invalid permutation cycle')
    return result


def reconstruct(chain, plans):
    require(isinstance(plans, list) and len(plans) == len(chain), 'wrong plan count')
    width = chain[0].tile.width
    parent = list(range(width))
    first = list(range(width))
    previous = first
    edges = []
    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v
    def union(a, b):
        a, b = root(a), root(b)
        if a != b:
            parent[max(a, b)] = min(a, b)
    def add(tile, vertices, edge_ids, left_indices, right_indices, tips):
        image = {}
        for v in vertices:
            image[v] = len(parent)
            parent.append(len(parent))
        for i in left_indices:
            union(image[tile.left[i]], tips[i])
        edges.extend((image[tile.edges[e][0]], image[tile.edges[e][1]])
                     for e in edge_ids)
        return {i: image[tile.right[i]] for i in right_indices}
    for block, plan in zip(chain, plans):
        tile = block.tile
        if plan.get('kind') == 'literal':
            require(type(plan.get('kept')) is int and
                    plan == {'kind': 'literal', 'kept': block.copies} and
                    block.copies <= 4, 'invalid literal block')
            tips = dict(enumerate(previous))
            for _ in range(block.copies):
                tips = add(tile, range(tile.n), range(len(tile.edges)),
                           range(width), range(width), tips)
            previous = [tips[i] for i in range(width)]
            continue
        require(plan.get('kind') == 'routed', 'unknown reduction')
        records, permutation = analyse(tile)
        expected_paths = []
        output = [None] * width
        for start in range(len(records)):
            cycle = orbit(permutation, start)
            quotient, remainder = divmod(block.copies, len(cycle))
            expected_paths.append({'start': start, 'cycle': cycle,
                                   'quotient': hex(quotient), 'remainder': remainder,
                                   'kept_periods': min(quotient, 4),
                                   'exit': cycle[remainder]})
            tips = {i: previous[i] for i in records[start]['left']}
            for j in range(len(cycle)*min(quotient, 4) + remainder):
                r = records[cycle[j % len(cycle)]]
                tips = add(tile, r['vertices'], r['edges'], r['left'], r['right'], tips)
            for i, v in tips.items():
                output[i] = v
        require(plan == {'kind': 'routed', 'permutation': permutation,
                         'paths': expected_paths}, 'routing plan does not match source')
        require(all(v is not None for v in output), 'uncovered output')
        previous = output
    for a, b in zip(previous, first):
        union(a, b)
    labels = {}
    image = []
    for v in range(len(parent)):
        rv = root(v)
        if rv not in labels:
            labels[rv] = len(labels)
        image.append(labels[rv])
    return Graph(len(labels), tuple((image[a], image[b]) for a, b in edges))


def verify_source_witness(chain, witness):
    """Return original edge addresses after checking every compressed seam."""
    validate_chain(chain)
    require(witness.get('schema') == 'routed-source-coloring-v1', 'wrong witness schema')
    require(witness.get('source_sha256') == source_digest(chain), 'source mismatch')
    blocks = witness.get('blocks')
    require(isinstance(blocks, list) and len(blocks) == len(chain), 'wrong block count')
    total_cost = 0
    flags = 0
    crossings = []
    anchors = {}
    first = None
    previous = None

    def process_edges(tile, edge_ids, mask, block_index, offset, stride, repeats):
        nonlocal total_cost, flags
        mixed = []
        for ei in edge_ids:
            a, b = tile.edges[ei]
            ca, cb = (mask >> a) & 1, (mask >> b) & 1
            if ca != cb:
                mixed.append(ei)
            else:
                flags |= 1 << ca
                anchors.setdefault(ca, {'block': block_index, 'copy': hex(offset), 'edge': ei})
        total_cost += len(mixed) * repeats
        require(total_cost <= 3, 'source cut is too large')
        if mixed:
            for j in range(repeats):  # repeats <= 3 proved immediately above.
                crossings.extend({'block': block_index, 'copy': hex(offset+j*stride),
                                  'edge': ei} for ei in mixed)

    for bi, (block, record) in enumerate(zip(chain, blocks)):
        tile = block.tile
        left_colors = [None] * tile.width
        right_colors = [None] * tile.width
        if record.get('kind') == 'literal':
            colors = record.get('colors')
            require(block.copies <= 4 and isinstance(colors, list) and
                    len(colors) == block.copies, 'invalid literal witness')
            last = None
            for copy, value in enumerate(colors):
                mask = integer_hex(value)
                require(mask < 1 << tile.n, 'color mask too long')
                left = [(mask >> v) & 1 for v in tile.left]
                right = [(mask >> v) & 1 for v in tile.right]
                require(last is None or left == last, 'literal seam mismatch')
                if copy == 0:
                    left_colors = left
                last = right
                process_edges(tile, range(len(tile.edges)), mask, bi, copy, 1, 1)
            right_colors = last
        else:
            require(record.get('kind') == 'routed', 'invalid witness kind')
            groups, permutation = analyse(tile)
            paths = record.get('paths')
            require(isinstance(paths, list) and len(paths) == len(groups), 'wrong path count')
            for start, path in enumerate(paths):
                require(type(path.get('start')) is int and path['start'] == start,
                        'path order mismatch')
                cycle = orbit(permutation, start)
                segments = path.get('segments')
                require(isinstance(segments, list) and 1 <= len(segments) <= 5,
                        'invalid segment count')
                phase = start
                offset = 0
                last = None
                for segment in segments:
                    word = segment.get('word')
                    repeat = integer_hex(segment.get('repeat'))
                    require(repeat >= 1 and isinstance(word, list) and
                            1 <= len(word) <= len(cycle), 'invalid word')
                    if repeat > 1:
                        require(len(word) == len(cycle), 'repeated word must be a full cycle')
                    begin_phase = phase
                    begin_colors = None
                    for j, value in enumerate(word):
                        group = groups[phase]
                        mask = integer_hex(value)
                        allowed = sum(1 << v for v in group['vertices'])
                        require(mask & ~allowed == 0, 'colors outside component')
                        left = {i: (mask >> tile.left[i]) & 1 for i in group['left']}
                        right = {i: (mask >> tile.right[i]) & 1 for i in group['right']}
                        require(last is None or left == last, 'routed seam mismatch')
                        if offset == 0 and j == 0:
                            for i, color in left.items():
                                left_colors[i] = color
                        if j == 0:
                            begin_colors = left
                        process_edges(tile, group['edges'], mask, bi, offset+j,
                                      len(word), repeat)
                        last = right
                        phase = permutation[phase]
                    if repeat > 1:
                        require(phase == begin_phase and begin_colors == last,
                                'repeated cycle colors do not agree')
                    offset += len(word)*repeat
                require(offset == block.copies, 'source exponent mismatch')
                for i, color in last.items():
                    require(right_colors[i] is None, 'duplicate output')
                    right_colors[i] = color
        require(all(c is not None for c in left_colors + right_colors), 'missing boundary colors')
        if first is None:
            first = left_colors
        require(previous is None or previous == left_colors, 'block colors disagree')
        previous = right_colors
    require(previous == first, 'closure colors disagree')
    require(flags == 3, 'both edge marks are required')
    return {'cost': total_cost, 'crossings': crossings, 'anchors': [anchors[0], anchors[1]]}


def verify_result(chain, result):
    try:
        validate_chain(chain)
        require(result.get('schema') == 'routed-cubic-cut-v1', 'wrong result schema')
        require(result.get('source_sha256') == source_digest(chain), 'source mismatch')
        graph = reconstruct(chain, result['plans'])
        require(result.get('kernel') == {'n': graph.n,
                                        'edges': [list(e) for e in graph.edges]},
                'kernel differs from independent reconstruction')
        _check_graph(graph, result['graph_proof'])
        if result['graph_proof']['verdict'] == 'LOW_CYCLIC_CUT':
            source = verify_source_witness(chain, result['source_witness'])
            require(source['cost'] == result['graph_proof']['cost'], 'lifted cost changed')
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False
