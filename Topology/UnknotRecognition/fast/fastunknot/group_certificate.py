"""Replayable cyclic-knot-group certificates, with bounded Whitehead search.

For validated classical one-component diagrams only. A knot in S^3 with
infinite cyclic group is the unknot (Loop Theorem). Every accepted trace
reduces the full Wirtinger presentation to one generator and no relations.
Stalling is inconclusive, including after Whitehead minimization. Explicit
relator expansion has no polynomial bound in the input crossing number.
"""
from collections import Counter, deque
from time import monotonic


class GroupLimit(RuntimeError):
    """A local resource allowance was exhausted; never a knot verdict."""


class _Budget:
    def __init__(self, check, max_letters, max_work):
        for name, value in (("max_letters", max_letters), ("max_work", max_work)):
            if type(value) is not int or value < 0:
                raise ValueError(f'{name} must be a nonnegative integer')
        self.check, self.max_letters, self.left = check, max_letters, max_work

    def tick(self, amount=1):
        self.check()
        self.left -= amount
        if self.left < 0:
            raise GroupLimit('group work allowance exhausted')

    def size(self, amount):
        self.tick()
        if amount > self.max_letters:
            raise GroupLimit('group expanded-letter allowance exhausted')


def _reduce(letters, budget):
    stack = []
    for i, x in enumerate(letters):
        if i % 256 == 0:
            budget.tick(256)
        if stack and stack[-1] == -x:
            stack.pop()
        else:
            stack.append(x)
    left, right = 0, len(stack)
    while right-left > 1 and stack[left] == -stack[right-1]:
        if left % 256 == 0:
            budget.tick(256)
        left, right = left+1, right-1
    return stack[left:right]


def _presentation(diagram, budget):
    from .diagram import DisjointSet

    n = diagram.crossings
    budget.size(4*n)
    if not n:
        return {1}, []
    components = DisjointSet(2*n)
    for _, b, _, d in diagram.pd:
        budget.tick()
        components.union(b, d)
    # Names are determined by the minimum arc label, not DSU root choices.
    names, owner = {}, {}
    for label in range(2*n):
        budget.tick()
        root = components.find(label)
        if root not in names:
            names[root] = len(names)+1
        owner[label] = names[root]
    words = []
    for row, (u, _), sign in zip(diagram.pd, diagram.incoming_slots(), diagram.signs()):
        a, b, c = owner[row[u]], owner[row[1]], owner[row[(u+2) % 4]]
        words.append(_reduce([b, a, -b, -c] if sign > 0 else [b, c, -b, -a], budget))
    return set(names.values()), words


def _whitehead_graph(words, budget):
    graph = {}
    for word in words:
        budget.tick(len(word)+1)
        for x in word:
            graph.setdefault(x, {})
            graph.setdefault(-x, {})
        for i, x in enumerate(word):
            y = -word[(i+1) % len(word)]
            graph[x][y] = graph[x].get(y, 0)+1
            graph[y][x] = graph[y].get(x, 0)+1
    return graph


def _mincut(graph, source, target, budget):
    """Edmonds--Karp on integer capacities; return the source-side cut."""
    residual = {u: dict(neighbors) for u, neighbors in graph.items()}
    while True:
        budget.tick()
        parent, queue = {source: None}, deque([source])
        while queue and target not in parent:
            u = queue.popleft()
            budget.tick(len(residual[u])+1)
            for v, capacity in residual[u].items():
                if capacity and v not in parent:
                    parent[v] = u
                    queue.append(v)
        if target not in parent:
            return set(parent)
        v, flow = target, None
        while parent[v] is not None:
            u = parent[v]
            flow = residual[u][v] if flow is None else min(flow, residual[u][v])
            v = u
        v = target
        while parent[v] is not None:
            u = parent[v]
            residual[u][v] -= flow
            residual[v][u] += flow
            v = u


def _whitehead_move(words, budget):
    graph = _whitehead_graph(words, budget)
    best = (0, None, None)
    for a in sorted(graph):
        subset = _mincut(graph, a, -a, budget)
        budget.tick(sum(len(graph[u]) for u in subset)+1)
        change = sum(w for u in subset for v, w in graph[u].items() if v not in subset)
        change -= sum(graph[a].values())
        if change < best[0]:
            best = change, a, subset
    return best


def _image(x, a, subset):
    if abs(x) == abs(a):
        return (x,)
    return ((-a,) if -x in subset else ()) + (x,) + ((a,) if x in subset else ())


def group_certificate(diagram, *, check=lambda: None, max_letters=200000, max_work=2000000):
    """Find a positive certificate, or None on a stalled search.

    Local size/work exhaustion raises GroupLimit. Caller cancellation is
    propagated. No relator is dropped except a verified defining relation.
    """
    budget = _Budget(check, max_letters, max_work)
    alive, words = _presentation(diagram, budget)
    moves = []
    while len(alive) > 1:
        counts, candidates = Counter(), []
        for word in words:
            budget.tick(len(word)+1)
            counts.update(map(abs, word))
        for i, word in enumerate(words):
            budget.tick(len(word)+1)
            for g, count in Counter(map(abs, word)).items():
                if count == 1:
                    candidates.append(((len(word)-2)*counts[g], len(word), i, g))
        if candidates:
            _, _, index, g = min(candidates)
            word = words[index]
            position = next(i for i, x in enumerate(word) if abs(x) == g)
            rest = word[position+1:] + word[:position]
            replacement = [-x for x in reversed(rest)] if word[position] > 0 else rest
            inverse = [-x for x in reversed(replacement)]
            words[index] = []
            expanded = sum(map(len, words))+(counts[g]-1)*(len(replacement)-1)
            budget.size(expanded)
            words = [_reduce((x for h in w for x in
                     (replacement if h == g else inverse if h == -g else (h,))), budget)
                     for w in words]
            alive.remove(g)
            moves.append(dict(kind='eliminate', relation=index, generator=g))
        else:
            change, a, subset = _whitehead_move(words, budget)
            if change >= 0:
                return None
            before = sum(map(len, words))
            # Conservative allocation bound before even constructing images.
            budget.size(3*before)
            words = [_reduce((y for x in w for y in _image(x, a, subset)), budget) for w in words]
            if sum(map(len, words))-before != change:
                raise ArithmeticError('Whitehead cut and literal substitution disagree')
            moves.append(dict(kind='whitehead', multiplier=a, subset=sorted(subset)))
    budget.tick()
    if any(words):
        return None
    return dict(version=1, method='wirtinger-cyclic-group', status='UNKNOT',
                input_pd=[list(row) for row in diagram.pd], moves=moves,
                remaining_generator=next(iter(alive)))


def verify_group_certificate(diagram, certificate, *, check=lambda: None,
                             max_letters=200000, max_work=2000000):
    """Independently reconstruct and replay; no producer algebra/search helpers.

    The shared budget helper only controls resources. Exhaustion raises
    GroupLimit; invalid evidence returns False. Input validity is the usual
    Diagram contract. All relators are reconstructed, including the redundant
    Wirtinger relation, and terminal freeness is checked explicitly.
    """
    budget = _Budget(check, max_letters, max_work)
    budget.tick()
    if (type(certificate) is not dict or set(certificate) != {
            'version', 'method', 'status', 'input_pd', 'moves', 'remaining_generator'}
            or type(certificate['version']) is not int or certificate['version'] != 1
            or certificate['method'] != 'wirtinger-cyclic-group'
            or certificate['status'] != 'UNKNOT'
            or certificate['input_pd'] != [list(row) for row in diagram.pd]
            or type(certificate['remaining_generator']) is not int
            or type(certificate['moves']) is not list):
        return False
    budget.tick(len(certificate['moves']))
    n = len(diagram.pd)
    budget.size(4*n)
    # Construct overpass arcs by graph traversal, independently of DSU.
    adjacency = {label: set() for row in diagram.pd for label in row}
    positions = {}
    for i, row in enumerate(diagram.pd):
        budget.tick()
        adjacency[row[1]].add(row[3])
        adjacency[row[3]].add(row[1])
        for j, label in enumerate(row):
            positions.setdefault(label, []).append(4*i+j)
    owner, count = {}, 0
    for label in sorted(adjacency):
        budget.tick()
        if label in owner:
            continue
        count += 1
        owner[label], pending = count, [label]
        while pending:
            budget.tick()
            for other in adjacency[pending.pop()]:
                if other not in owner:
                    owner[other] = count
                    pending.append(other)
    # Trace the oriented component from dart zero, without Diagram caches.
    mates = {}
    for ends in positions.values():
        if len(ends) != 2:
            return False
        a, b = ends
        mates[a], mates[b] = b, a
    incoming, current = [set() for _ in range(n)], 0
    for _ in range(2*n):
        budget.tick()
        incoming[current//4].add(current % 4)
        current = mates[4*(current//4)+(current+2) % 4]
    if current != 0:
        return False

    def normalize(letters):
        # Deque implementation deliberately separate from producer reduction.
        result = deque()
        for i, x in enumerate(letters):
            if i % 256 == 0:
                budget.tick(256)
            if result and result[-1]+x == 0:
                result.pop()
            else:
                result.append(x)
        i = 0
        while len(result) > 1 and result[0]+result[-1] == 0:
            if i % 256 == 0:
                budget.tick(256)
            result.popleft()
            result.pop()
            i += 1
        return list(result)

    words = []
    for row, ports in zip(diagram.pd, incoming):
        under = ports & {0, 2}
        over = ports & {1, 3}
        if len(under) != 1 or len(over) != 1:
            return False
        u, o = under.pop(), over.pop()
        left, right, top = owner[row[u]], owner[row[(u+2) % 4]], owner[row[o]]
        if (o-u) % 4 == 1:
            left, right = right, left
        words.append(normalize([top, left, -top, -right]))
    alive = set(range(1, count+1)) if n else {1}
    for move in certificate['moves']:
        budget.tick()
        if type(move) is not dict:
            return False
        kind = move.get('kind')
        if kind == 'eliminate':
            if set(move) != {'kind', 'relation', 'generator'}:
                return False
            index, g = move['relation'], move['generator']
            if (type(index) is not int or not 0 <= index < len(words)
                    or type(g) is not int or g not in alive):
                return False
            positions_g = [i for i, x in enumerate(words[index]) if abs(x) == g]
            if len(positions_g) != 1:
                return False
            pos, pivot = positions_g[0], words[index]
            suffix, prefix = pivot[pos+1:], pivot[:pos]
            # Solve prefix*g^epsilon*suffix=1, preserving multiplication order.
            value = ([-x for x in reversed(prefix)]+[-x for x in reversed(suffix)]
                     if pivot[pos] == g else suffix+prefix)
            images = {g: value, -g: [-x for x in reversed(value)]}
            words[index] = []
            alive.remove(g)
        elif kind == 'whitehead':
            if set(move) != {'kind', 'multiplier', 'subset'}:
                return False
            a, subset = move['multiplier'], move['subset']
            if type(subset) is list:
                budget.tick(len(subset))
            if (type(a) is not int or abs(a) not in alive or type(subset) is not list
                    or any(type(x) is not int or abs(x) not in alive for x in subset)
                    or len(set(subset)) != len(subset) or a not in subset or -a in subset):
                return False
            subset = set(subset)
            images = {}
            for g in alive:
                image = [g]
                if g != abs(a):
                    if -g in subset:
                        image.insert(0, -a)
                    if g in subset:
                        image.append(a)
                images[g] = image
                images[-g] = [-x for x in reversed(image)]
        else:
            return False
        expanded = 0
        for word in words:
            budget.tick(len(word)+1)
            expanded += sum(len(images.get(x, (x,))) for x in word)
        budget.size(expanded)
        words = [normalize(y for x in word for y in images.get(x, (x,))) for word in words]
    budget.tick()
    return alive == {certificate['remaining_generator']} and not any(words)


def group_decide(diagram, *, seconds=0.05, max_letters=200000, max_work=2000000,
                 check=lambda: None):
    """Bounded search AND independent verification sharing one wall allowance."""
    from math import isfinite
    start = monotonic()
    if seconds is not None and (type(seconds) not in (int, float)
            or not isfinite(seconds) or seconds < 0):
        raise ValueError('group seconds must be finite and nonnegative, or None')
    expires = None if seconds is None else start+seconds

    def tick():
        check()
        if expires is not None and monotonic() >= expires:
            raise GroupLimit('group local time allowance exhausted')

    try:
        certificate = group_certificate(diagram, check=tick, max_letters=max_letters, max_work=max_work)
        if certificate is not None:
            valid = verify_group_certificate(diagram, certificate, check=tick,
                                              max_letters=max_letters, max_work=max_work)
            tick()
            if not valid:
                raise ArithmeticError('produced group certificate failed independent replay')
            return dict(status='UNKNOT', certificate=certificate, seconds=monotonic()-start)
        reason = 'group simplification stalled'
    except GroupLimit as exc:
        check()  # A simultaneous global cancellation must still propagate.
        reason = str(exc)
    check()
    return dict(status='INCONCLUSIVE', reason=reason, seconds=monotonic()-start)
