"""Certified square-root-frontier orders for closed classical PD projections.

BFS layers restrict radius; a centroid of the triangulated dual cotree supplies
three short primal tree paths. Recursive balanced separators bound the crossing
frontier, not the number of surviving Khovanov generators. This order need not
have connected or common-disk prefixes. No recognition-time claim follows.
"""
from collections import defaultdict
from hashlib import sha256
from math import isqrt

from .ordering import best_scan_order, order_profile, validate_order


def _digest(pd):
    return sha256(repr(tuple(tuple(row) for row in pd)).encode()).hexdigest()


def _data(rotation, twin):
    tail = {d: v for v, darts in rotation.items() for d in darts}
    nxt = {d: darts[(i + 1) % len(darts)]
           for darts in rotation.values() for i, d in enumerate(darts)}
    return tail, nxt


def _faces(rotation, twin, check):
    _, nxt = _data(rotation, twin)
    face, cycles = {}, []
    for start in nxt:
        check()
        if start in face:
            continue
        cycle, d = [], start
        while d not in face:
            check()
            face[d] = len(cycles)
            cycle.append(d)
            d = nxt[twin[d]]
        if d != start:
            raise ArithmeticError('invalid face cycle')
        cycles.append(cycle)
    return face, cycles


def _adjacency(rotation, twin):
    tail, _ = _data(rotation, twin)
    return {v: {tail[twin[d]] for d in darts} - {v} for v, darts in rotation.items()}


def _components(vertices, adjacency, check):
    unseen, parts = set(vertices), []
    for root in sorted(unseen):
        check()
        if root not in unseen:
            continue
        unseen.remove(root)
        part, queue = {root}, [root]
        for v in queue:
            check()
            for w in adjacency[v]:
                if w in unseen:
                    unseen.remove(w)
                    part.add(w)
                    queue.append(w)
        parts.append(part)
    return parts


def _restrict(rotation, twin, vertices, tail=None):
    if tail is None:
        tail, _ = _data(rotation, twin)
    out = {v: [d for d in rotation[v] if tail[twin[d]] in vertices] for v in sorted(vertices)}
    keep = {d for darts in out.values() for d in darts}
    return out, {d: twin[d] for d in keep}


def _embedding(pd, check):
    occurrence = defaultdict(list)
    rotation = {}
    for v, row in enumerate(pd):
        check()
        if len(row) != 4 or any(type(x) is not int for x in row):
            raise ValueError('crossings require four integer labels')
        rotation[v] = list(range(4*v, 4*v+4))
        for d, label in zip(rotation[v], row):
            occurrence[label].append(d)
    if any(len(ds) != 2 for ds in occurrence.values()):
        raise ValueError('closed PD edges must occur twice')
    twin = {a: b for ds in occurrence.values() for a, b in (ds, ds[::-1])}
    adjacency = _adjacency(rotation, twin)
    parts = _components(rotation, adjacency, check)
    _, faces = _faces(rotation, twin, check)
    if len(rotation) - len(twin)//2 + len(faces) != 2*len(parts):
        raise ValueError('PD rotation system is not spherical')
    # Loops affect neither a vertex separator nor a crossing frontier.
    rotation = {v: [d for d in ds if twin[d]//4 != v] for v, ds in rotation.items()}
    keep = {d for ds in rotation.values() for d in ds}
    return rotation, {d: twin[d] for d in keep}, adjacency, parts


def _bfs(rotation, twin, root, check):
    tail, _ = _data(rotation, twin)
    distance, parent, tree = {root: 0}, {root: None}, set()
    queue = [root]
    for v in queue:
        check()
        for d in rotation[v]:
            w = tail[twin[d]]
            if w not in distance:
                distance[w] = distance[v]+1
                parent[w] = v
                tree.add(min(d, twin[d]))
                queue.append(w)
    if len(distance) != len(rotation):
        raise ArithmeticError('separator graph must be connected')
    return distance, parent, tree


def _contract_ball(rotation, twin, distance, tree, lower, root, check):
    """Contract the inner BFS tree by following its ribbon boundary once."""
    tail, nxt = _data(rotation, twin)
    removed = {d for d in twin if min(d, twin[d]) in tree
               and distance[tail[d]] <= lower and distance[tail[twin[d]]] <= lower}
    remaining = set(twin)-removed
    successor = {}
    for d in remaining:
        check()
        e = nxt[d]
        while e in removed:
            check()
            e = nxt[twin[e]]
        successor[d] = e
    new_tail = {d: root if distance[tail[d]] <= lower else tail[d] for d in remaining}
    out = {v: [] for v in rotation if distance[v] > lower}
    out[root] = []
    unseen = set(remaining)
    for start in sorted(remaining):
        if start not in unseen:
            continue
        v, d = new_tail[start], start
        if out[v]:
            raise ArithmeticError('tree contraction split a vertex rotation')
        while d in unseen:
            check()
            if new_tail[d] != v:
                raise ArithmeticError('contracted rotation changes vertex')
            unseen.remove(d)
            out[v].append(d)
            d = successor[d]
        if d != start:
            raise ArithmeticError('contracted rotation does not close')
    # Non-tree edges inside the ball have become loops and can be deleted.
    out = {v: [d for d in ds if new_tail[d] != new_tail[twin[d]]] for v, ds in out.items()}
    keep = {d for ds in out.values() for d in ds}
    return out, {d: twin[d] for d in keep}


def _path_separator(rotation, twin, root, weighted, check):
    """Three root paths at a weighted centroid face of a dual cotree."""
    if len(rotation) == 1:
        return set(rotation) & weighted
    tail, _ = _data(rotation, twin)
    _, faces = _faces(rotation, twin, check)
    new_rotation = {v: [] for v in rotation}
    new_twin = dict(twin)
    next_vertex, next_dart = max(rotation)+1, max(twin)+1
    spoke = {}
    for cycle in faces:
        check()
        center = next_vertex
        next_vertex += 1
        center_darts = []
        for d in cycle:
            check()
            a, b = next_dart, next_dart+1
            next_dart += 2
            spoke[d] = a
            new_twin[a], new_twin[b] = b, a
            center_darts.append(b)
        new_rotation[center] = list(reversed(center_darts))
    for v, ds in rotation.items():
        for d in ds:
            new_rotation[v].extend((spoke[d], d))
    face, triangles = _faces(new_rotation, new_twin, check)
    if any(len(cycle) != 3 for cycle in triangles):
        raise ArithmeticError('face-star triangulation failed')
    new_tail, _ = _data(new_rotation, new_twin)
    _, parent, tree = _bfs(new_rotation, new_twin, root, check)
    dual = [[] for _ in triangles]
    for d, e in new_twin.items():
        check()
        if d < e and d not in tree:
            a, b = face[d], face[e]
            dual[a].append(b)
            dual[b].append(a)
    if sum(map(len, dual)) != 2*(len(dual)-1):
        raise ArithmeticError('non-tree dual edges do not form a cotree')
    order, ancestors = [0], {0: None}
    for f in order:
        check()
        for g in dual[f]:
            if g not in ancestors:
                ancestors[g] = f
                order.append(g)
    if len(order) != len(dual):
        raise ArithmeticError('dual cotree is disconnected')
    weight = [0]*len(dual)
    for v in weighted:
        weight[face[new_rotation[v][0]]] += 1
    for f in reversed(order[1:]):
        weight[ancestors[f]] += weight[f]
    total = len(weighted)
    center = next(f for f in order if 2*max(
        [total-weight[f]] + [weight[g] for g in dual[f] if ancestors.get(g) == f]) <= total)
    separator = set()
    for d in triangles[center]:
        v = new_tail[d]
        while v is not None:
            check()
            separator.add(v)
            v = parent[v]
    return separator & weighted


def _separator(rotation, twin, check):
    n, root = len(rotation), min(rotation)
    distance, _, tree = _bfs(rotation, twin, root, check)
    levels = [[] for _ in range(max(distance.values())+1)]
    for v, level in distance.items():
        levels[level].append(v)
    total = 0
    for median, level in enumerate(levels):
        total += len(level)
        if 2*total >= n:
            break
    radius = isqrt(n-1)+1
    lower = -1 if median < radius else min(range(median-radius, median), key=lambda i: (len(levels[i]), i))
    upper = (len(levels) if median+radius >= len(levels) else
             min(range(median+1, median+radius+1), key=lambda i: (len(levels[i]), i)))
    separator = set(levels[lower] if lower >= 0 else ())
    if upper < len(levels):
        separator.update(levels[upper])
    weighted = {v for v in rotation if lower < distance[v] < upper}
    band, band_twin = _restrict(rotation, twin, {v for v in rotation if distance[v] < upper})
    if lower >= 0:
        band, band_twin = _contract_ball(band, band_twin, distance, tree, lower, root, check)
    separator.update(_path_separator(band, band_twin, root, weighted, check))
    adjacency = _adjacency(rotation, twin)
    parts = _components(set(rotation)-separator, adjacency, check)
    if any(2*len(part) > n for part in parts):
        raise ArithmeticError('constructed separator is not half-balanced')
    if len(separator) > 8*radius+6:
        raise ArithmeticError('constructed separator exceeds its size bound')
    return separator, parts


def separator_scan_order(pd, *, leaf_size=8, check=lambda: None):
    """Return an independently verifiable hierarchy and O(sqrt(n)) frontier order.

    The constant-size leaf cutoff is limited to 64. Children precede separator
    vertices; the bound is four times the largest separator-plus-leaf path sum.
    Caller-supplied check may raise a global resource exception at any stage.
    """
    if type(leaf_size) is not int or not 1 <= leaf_size <= 64:
        raise ValueError('leaf_size must be an integer from 1 through 64')
    pd = [tuple(row) for row in pd]
    check()
    rotation, twin, _, parts = _embedding(pd, check)
    def build(rot, twins):
        check()
        if len(rot) <= leaf_size:
            return dict(leaf=sorted(rot))
        separator, children = _separator(rot, twins, check)
        tail, _ = _data(rot, twins)
        return dict(separator=sorted(separator), children=[build(*_restrict(rot, twins, part, tail)) for part in children])
    tail, _ = _data(rotation, twin)
    forest = [build(*_restrict(rotation, twin, part, tail)) for part in parts]
    order = []
    def flatten(node):
        if 'leaf' in node:
            order.extend(node['leaf'])
            return 4*len(node['leaf'])
        bounds = [flatten(child) for child in node['children']]
        order.extend(node['separator'])
        return 4*len(node['separator'])+max(bounds, default=0)
    bound = max((flatten(node) for node in forest), default=0)
    result = dict(algorithm='bfs-dual-centroid-v1', pd_sha256=_digest(pd), leaf_size=leaf_size,
                  forest=forest, order=order, width_bound=bound, profile=list(order_profile(pd, order)))
    if not verify_separator_order(pd, result, check=check):
        raise ArithmeticError('separator hierarchy failed independent verification')
    return result


def verify_separator_order(pd, certificate, *, check=lambda: None):
    """Check graph partitions, balance, size, order and width without planar maps."""
    # This verifier intentionally does not call any separator/map constructor.
    try:
        pd = [tuple(row) for row in pd]
        n = len(pd)
        check()
        if certificate['algorithm'] != 'bfs-dual-centroid-v1' or certificate['pd_sha256'] != _digest(pd):
            return False
        leaf_size = certificate['leaf_size']
        if type(leaf_size) is not int or not 1 <= leaf_size <= 64:
            return False
        owners = defaultdict(list)
        for v, row in enumerate(pd):
            if len(row) != 4 or any(type(x) is not int for x in row):
                return False
            for label in row:
                owners[label].append(v)
        adjacency = {v: set() for v in range(n)}
        for ends in owners.values():
            if len(ends) != 2:
                return False
            u, v = ends
            adjacency[u].add(v)
            adjacency[v].add(u)
        seen, order = set(), []
        def take(values):
            if not isinstance(values, list) or any(type(v) is not int or not 0 <= v < n or v in seen for v in values):
                raise ValueError('invalid hierarchy vertex')
            if len(set(values)) != len(values):
                raise ValueError('duplicate hierarchy vertex')
            seen.update(values)
            return set(values)
        def visit(node):
            check()
            if set(node) == {'leaf'}:
                vertices = take(node['leaf'])
                if not vertices or len(vertices) > leaf_size:
                    raise ValueError('invalid leaf size')
                order.extend(node['leaf'])
                return vertices, 4*len(vertices)
            if set(node) != {'separator', 'children'} or not isinstance(node['children'], list):
                raise ValueError('invalid split node')
            separator = take(node['separator'])
            children = [visit(child) for child in node['children']]
            vertices = separator.union(*(part for part, _ in children))
            if len(vertices) <= leaf_size or len(separator) > 8*(isqrt(len(vertices)-1)+1)+6:
                raise ValueError('invalid separator size')
            if any(2*len(part) > len(vertices) for part, _ in children):
                raise ValueError('unbalanced child')
            actual = {frozenset(p) for p in _components(vertices-separator, adjacency, check)}
            if actual != {frozenset(part) for part, _ in children}:
                raise ValueError('children do not equal the remaining graph components')
            order.extend(node['separator'])
            return vertices, 4*len(separator)+max((b for _, b in children), default=0)
        roots = [visit(node) for node in certificate['forest']]
        if {frozenset(p) for p in _components(range(n), adjacency, check)} != {frozenset(p) for p, _ in roots}:
            return False
        validate_order(n, certificate['order'])
        profile = list(order_profile(pd, order))
        bound = max((b for _, b in roots), default=0)
        return (order == certificate['order'] and len(seen) == n and certificate['profile'] == profile
                and type(certificate['width_bound']) is int and certificate['width_bound'] == bound
                and profile[0] <= bound)
    except (KeyError, TypeError, ValueError, RecursionError):
        return False


def width_bounded_scan_order(pd, *, order=None, tries=12, leaf_size=8, check=lambda: None):
    """Choose the smaller profile of the certified order and a greedy order.

    The separator witness makes the selected frontier bound independently
    checkable even when the smaller practical order comes from the heuristic.
    This is opt-in preparation for any scanner accepting an explicit order.
    """
    pd = [tuple(row) for row in pd]
    if type(tries) is not int or tries < 1:
        raise ValueError('tries must be a positive integer')
    separator = separator_scan_order(pd, leaf_size=leaf_size, check=check)
    candidate = (best_scan_order(pd, tries=tries, check=check) if order is None
                 else validate_order(len(pd), order))
    profile = list(order_profile(pd, candidate))
    selected = ('greedy' if order is None else 'supplied') if profile <= separator['profile'] else 'separator'
    order = candidate if selected != 'separator' else separator['order']
    return dict(order=order, selected=selected, profile=list(order_profile(pd, order)),
                width_bound=separator['width_bound'], separator=separator)


def verify_width_bounded_order(pd, certificate, *, check=lambda: None):
    """Verify the witness and domination by its actual frontier profile."""
    try:
        if not verify_separator_order(pd, certificate['separator'], check=check):
            return False
        order = validate_order(len(pd), certificate['order'])
        profile = list(order_profile(pd, order))
        return (profile == certificate['profile'] and profile <= certificate['separator']['profile']
                and certificate['width_bound'] == certificate['separator']['width_bound']
                and certificate['selected'] in ('greedy', 'supplied', 'separator'))
    except (KeyError, TypeError, ValueError):
        return False
