"""Polynomial marked-cut kernels for component-routed graph tile powers.

Input components must induce the same unordered partition of the left and
right interface indices.  Components can have different interface widths.
The result is a graph-query certificate, not a three-manifold certificate.
"""
from __future__ import annotations

from pattern_kernel.core import (
    Block, Graph, Tile, DSU, natural, source_digest, validate_chain,
    certify_cubic_graph,
)


def components(tile: Tile) -> dict:
    """Find components by graph traversal and validate interface alignment."""
    adjacency = [[] for _ in range(tile.n)]
    for a, b in tile.edges:
        adjacency[a].append(b)
        adjacency[b].append(a)
    unseen = set(range(tile.n))
    groups = []
    while unseen:
        seed = min(unseen)
        unseen.remove(seed)
        vertices = {seed}
        stack = [seed]
        while stack:
            for v in adjacency[stack.pop()]:
                if v in unseen:
                    unseen.remove(v)
                    vertices.add(v)
                    stack.append(v)
        left = tuple(i for i, v in enumerate(tile.left) if v in vertices)
        right = tuple(i for i, v in enumerate(tile.right) if v in vertices)
        if not left or not right:
            raise ValueError('every component must meet both interfaces')
        groups.append({'vertices': sorted(vertices), 'left': left, 'right': right})
    groups.sort(key=lambda item: item['left'])
    by_left = {item['left']: i for i, item in enumerate(groups)}
    if set(by_left) != {item['right'] for item in groups}:
        raise ValueError('component interface partitions do not align')
    owner = {}
    for i, item in enumerate(groups):
        item['edges'] = []
        for v in item['vertices']:
            owner[v] = i
    for ei, (a, _) in enumerate(tile.edges):
        groups[owner[a]]['edges'].append(ei)
    permutation = [by_left[item['right']] for item in groups]
    return {'groups': groups, 'permutation': permutation}


def cycle_at(permutation: list[int], start: int) -> list[int]:
    cycle = [start]
    nxt = permutation[start]
    while nxt != start:
        cycle.append(nxt)
        nxt = permutation[nxt]
    return cycle


def connected_cutoff(threshold: int) -> int:
    """Optimal universal unit-edge cutoff for the two exact edge marks."""
    if type(threshold) is not int or threshold < 0:
        raise ValueError('nonnegative integer threshold required')
    return (1, 3, 4)[threshold] if threshold < 3 else threshold + 1


def plan_block(block: Block, threshold: int = 3) -> tuple[dict, dict | None]:
    limit = connected_cutoff(threshold)
    try:
        data = components(block.tile)
    except ValueError:
        if block.copies > limit:
            raise
        return {'kind': 'literal', 'kept': block.copies}, None
    paths = []
    for start in range(len(data['groups'])):
        cycle = cycle_at(data['permutation'], start)
        quotient, remainder = divmod(block.copies, len(cycle))
        paths.append({'start': start, 'cycle': cycle,
                      'quotient': hex(quotient), 'remainder': remainder,
                      'kept_periods': min(quotient, limit),
                      'exit': cycle[remainder]})
    return {'kind': 'routed', 'permutation': data['permutation'],
            'paths': paths}, data


def build_kernel(chain: tuple[Block, ...], threshold: int = 3, *,
                 close: bool = True) -> tuple[Graph | Tile, list[dict], list[dict]]:
    """Build only retained fragments; no loop depends on an input exponent."""
    validate_chain(chain, cubic=False)
    edges = []
    vertex_count = chain[0].tile.width
    first = list(range(vertex_count))
    previous = first
    plans = []
    views = []

    def occurrence(tile, vertices, edge_ids, left_indices, right_indices, tips):
        nonlocal vertex_count
        image = {}
        for i in left_indices:
            image[tile.left[i]] = tips[i]
        for v in vertices:
            if v not in image:
                image[v] = vertex_count
                vertex_count += 1
        edges.extend((image[tile.edges[e][0]], image[tile.edges[e][1]])
                     for e in edge_ids)
        output = {i: image[tile.right[i]] for i in right_indices}
        return image, output

    for block in chain:
        tile = block.tile
        plan, data = plan_block(block, threshold)
        plans.append(plan)
        if plan['kind'] == 'literal':
            images = []
            tips = dict(enumerate(previous))
            for _ in range(plan['kept']):
                image, tips = occurrence(tile, range(tile.n), range(len(tile.edges)),
                                         range(tile.width), range(tile.width), tips)
                images.append(image)
            previous = [tips[i] for i in range(tile.width)]
            views.append({'kind': 'literal', 'images': images})
            continue
        output = [None] * tile.width
        path_views = []
        for path in plan['paths']:
            start = path['start']
            cycle = path['cycle']
            start_group = data['groups'][start]
            tips = {i: previous[i] for i in start_group['left']}
            length = len(cycle) * path['kept_periods'] + path['remainder']
            images = []
            for j in range(length):
                group = data['groups'][cycle[j % len(cycle)]]
                image, tips = occurrence(tile, group['vertices'], group['edges'],
                                         group['left'], group['right'], tips)
                images.append(image)
            for i, v in tips.items():
                output[i] = v
            path_views.append(images)
        if any(v is None for v in output):
            raise AssertionError('routing did not cover the output interface')
        previous = output
        views.append({'kind': 'routed', 'paths': path_views})
    if not close:
        return Tile(vertex_count, tuple(edges), tuple(first), tuple(previous)), plans, views
    dsu = DSU(vertex_count)
    for a, b in zip(previous, first):
        dsu.union(a, b)
    names = {}
    image = []
    for v in range(vertex_count):
        root = dsu.find(v)
        if root not in names:
            names[root] = len(names)
        image.append(names[root])
    for view in views:
        lists = [view['images']] if view['kind'] == 'literal' else view['paths']
        for images in lists:
            for local in images:
                for v, global_v in local.items():
                    local[v] = image[global_v]
    return Graph(len(names), tuple((image[a], image[b]) for a, b in edges)), plans, views


def _mask(local: dict[int, int], shore: set[int]) -> int:
    return sum(1 << v for v, image in local.items() if image in shore)


def source_witness(chain, plans, views, shore: list[int]) -> dict:
    selected = set(shore)
    blocks = []
    for block, plan, view in zip(chain, plans, views):
        if plan['kind'] == 'literal':
            blocks.append({'kind': 'literal', 'colors': [hex(_mask(x, selected))
                                                       for x in view['images']]})
            continue
        data = components(block.tile)
        paths = []
        for path, images in zip(plan['paths'], view['paths']):
            h = len(path['cycle'])
            q = int(path['quotient'], 16)
            masks = [_mask(local, selected) for local in images]
            periods = [masks[j*h:(j+1)*h] for j in range(path['kept_periods'])]
            repeats = [1] * len(periods)
            if q > len(periods):
                for j, word in enumerate(periods):
                    cost = 0
                    for c, mask in zip(path['cycle'], word):
                        for ei in data['groups'][c]['edges']:
                            a, b = block.tile.edges[ei]
                            cost += ((mask >> a) ^ (mask >> b)) & 1
                    if cost == 0:
                        repeats[j] += q - len(periods)
                        break
                else:
                    raise AssertionError('no zero-cost full cycle in a small cut')
            segments = [{'word': [hex(mask) for mask in word], 'repeat': hex(repeat)}
                        for word, repeat in zip(periods, repeats)]
            tail = masks[path['kept_periods']*h:]
            if tail:
                segments.append({'word': [hex(mask) for mask in tail], 'repeat': '0x1'})
            paths.append({'start': path['start'], 'segments': segments})
        blocks.append({'kind': 'routed', 'paths': paths})
    return {'schema': 'routed-source-coloring-v1',
            'source_sha256': source_digest(chain), 'blocks': blocks}


def solve(chain: tuple[Block, ...]) -> dict:
    validate_chain(chain)
    graph, plans, views = build_kernel(chain)
    proof = certify_cubic_graph(graph)
    result = {'schema': 'routed-cubic-cut-v1', 'source_sha256': source_digest(chain),
              'plans': plans, 'kernel': {'n': graph.n, 'edges': [list(e) for e in graph.edges]},
              'graph_proof': proof}
    if proof['verdict'] == 'LOW_CYCLIC_CUT':
        result['source_witness'] = source_witness(chain, plans, views, proof['shore'])
    return result


def parse_chain(payload: dict) -> tuple[Block, ...]:
    if payload.get('schema') != 'closed-tile-chain-v1':
        raise ValueError('unknown source schema')
    output = []
    for item in payload['blocks']:
        t = item['tile']
        tile = Tile(t['n'], tuple(tuple(e) for e in t['edges']),
                    tuple(t['left']), tuple(t['right']))
        output.append(Block(tile, natural(item['copies'])))
    return tuple(output)
