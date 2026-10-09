"""Replayable cyclic-knot-group certificates, with bounded Whitehead search.

For validated classical one-component diagrams only. A knot in S^3 with
infinite cyclic group is the unknot (Loop Theorem). Legacy traces reduce
the full presentation to one generator and no relations. Version five instead
checks a primitive-power relator at rank two after full prefix replay; knot
group torsion-freeness and abelianization then imply infinite cyclicity.
Version six also replays complete disjoint primitive-pair projections and
checks raw one-generator exponent endpoints without discarding relator slots.
Version seven also permits acyclic unit-coordinate forests whose donors may
share generators. Version eight permits acyclic singleton definitions with
arbitrary word images, compiled as one simultaneous raw substitution.
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
    return _whitehead_cut(_whitehead_graph(words, budget), budget)


def _whitehead_cut(graph, budget):
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


def group_certificate(diagram, *, check=lambda: None, max_letters=200000, max_work=2000000,
                      relator_moves=False, adaptive=False, switch_letters=None,
                      max_nodes=100000, stats=None):
    """Find a positive certificate, or None on a stalled search.

    Local size/work exhaustion raises GroupLimit. Caller cancellation is
    propagated. No relator is dropped except a verified defining relation.
    Adaptive mode switches once, before a predicted substitution allocation
    exceeds switch_letters (default max_letters). This does not reset budgets.
    """
    budget = _Budget(check, max_letters, max_work)
    if type(relator_moves) is not bool:
        raise ValueError('relator_moves must be boolean')
    if type(adaptive) is not bool:
        raise ValueError('adaptive must be boolean')
    if switch_letters is not None and (type(switch_letters) is not int or switch_letters < 0):
        raise ValueError('switch_letters must be a nonnegative integer or None')
    if switch_letters is not None and not adaptive:
        raise ValueError('switch_letters requires adaptive search')
    if type(max_nodes) is not int or max_nodes < 0:
        raise ValueError('max_nodes must be a nonnegative integer')
    if stats is not None and type(stats) is not dict:
        raise ValueError('stats must be a dictionary or None')
    threshold = max_letters if switch_letters is None else min(switch_letters, max_letters)
    if stats is not None:
        stats.update(representation='explicit', switched=False)
    alive, words = _presentation(diagram, budget)
    moves = []

    def handoff(kind, projected):
        from .compressed_search import _continue_compressed
        if stats is not None:
            stats.update(representation='compressed-slp', switched=True,
                switch=dict(kind=kind, before_move=len(moves), generators=len(alive),
                            current_letters=sum(map(len, words)), projected_letters=projected,
                            threshold=threshold, explicit_work=max_work-budget.left,
                            remaining_work=budget.left))
        return _continue_compressed(words, alive, moves, budget, max_nodes, relator_moves, stats)

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
            expanded = sum(map(len, words))-len(word)+(counts[g]-1)*(len(word)-2)
            if adaptive and expanded > threshold:
                if not handoff('eliminate', expanded):
                    return None
                words = []  # Continuation proved all relators empty and rank one.
                break
            budget.size(expanded)
            position = next(i for i, x in enumerate(word) if abs(x) == g)
            rest = word[position+1:] + word[:position]
            replacement = [-x for x in reversed(rest)] if word[position] > 0 else rest
            inverse = [-x for x in reversed(replacement)]
            words[index] = []
            words = [_reduce((x for h in w for x in
                     (replacement if h == g else inverse if h == -g else (h,))), budget)
                     for w in words]
            alive.remove(g)
            moves.append(dict(kind='eliminate', relation=index, generator=g))
        else:
            # Small-rank cuts are cheap, and preserve the earlier successful
            # paths. At larger rank, try linear-space overlap matching before
            # paying for one flow per signed generator. Six is an empirical
            # dispatch threshold, not a theorem about presentation complexity.
            whitehead = (_whitehead_move(words, budget)
                         if not relator_moves or len(alive) <= 6 else None)
            if relator_moves and (whitehead is None or whitehead[0] >= 0):
                from .relator_overlap import overlap_move, apply_overlap
                move = overlap_move(words, budget)
                if move is not None:
                    apply_overlap(words, move, budget, _reduce)
                    moves.append(move)
                    continue
            if whitehead is None:
                whitehead = _whitehead_move(words, budget)
            change, a, subset = whitehead
            if change >= 0:
                return None
            before = sum(map(len, words))
            # Conservative allocation bound before even constructing images.
            if adaptive and 3*before > threshold:
                if not handoff('whitehead', 3*before):
                    return None
                words = []
                break
            budget.size(3*before)
            words = [_reduce((y for x in w for y in _image(x, a, subset)), budget) for w in words]
            if sum(map(len, words))-before != change:
                raise ArithmeticError('Whitehead cut and literal substitution disagree')
            moves.append(dict(kind='whitehead', multiplier=a, subset=sorted(subset)))
    budget.tick()
    if stats is not None:
        stats.update(work=max_work-budget.left, moves=len(moves))
    if any(words):
        return None
    return dict(version=_certificate_version(moves),
                method='wirtinger-cyclic-group', status='UNKNOT',
                input_pd=[list(row) for row in diagram.pd], moves=moves,
                remaining_generator=next(iter(alive)))


def _certificate_version(moves):
    if any(m['kind'] == 'relator_power' for m in moves):
        return 4
    if any(m['kind'] == 'whitehead_power' for m in moves):
        return 3
    return 2 if any(m['kind'] == 'relator' for m in moves) else 1


def verify_group_certificate(diagram, certificate, *, check=lambda: None,
                             max_letters=200000, max_work=2000000,
                             compressed=False, max_nodes=100000, stats=None):
    """Independently reconstruct and replay; no producer algebra/search helpers.

    The shared budget helper only controls resources. Exhaustion raises
    GroupLimit; invalid evidence returns False. Input validity is the usual
    Diagram contract. All relators are reconstructed, including the redundant
    Wirtinger relation. Legacy terminal freeness is checked explicitly; version
    five independently verifies a primitive-power relation at rank two and
    uses the reconstructed knot-group provenance to conclude cyclicity.
    Version six also checks simultaneous primitive-pair projections, explicit
    normalization handoffs and raw one-generator zero-exponent endpoints.

    With compressed=True, reconstruct the same initial presentation but
    replay it as exact straight-line-program words. max_letters then bounds
    only the initial presentation; max_nodes bounds compressed storage and
    equality assertions. The search backend is selected separately.
    """
    if type(compressed) is not bool:
        raise ValueError('compressed must be boolean')
    if type(max_nodes) is not int or max_nodes < 0:
        raise ValueError('max_nodes must be a nonnegative integer')
    if stats is not None and type(stats) is not dict:
        raise ValueError('stats must be a dictionary or None')
    budget = _Budget(check, max_letters, max_work)
    budget.tick()
    if type(certificate) is not dict or type(certificate.get('version')) is not int:
        return False
    version = certificate['version']
    final_field = 'terminal' if version in (5, 6, 7, 8, 9, 10) else 'remaining_generator'
    if (set(certificate) != {'version', 'method', 'status', 'input_pd', 'moves', final_field}
            or version not in (1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
            or certificate['method'] != 'wirtinger-cyclic-group'
            or certificate['status'] != 'UNKNOT'
            or certificate['input_pd'] != [list(row) for row in diagram.pd]
            or (version < 5 and type(certificate['remaining_generator']) is not int)
            or (version >= 5 and type(certificate['terminal']) is not dict)
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
    if compressed:
        from .compressed_group import verify_moves, CompressedLimit
        try:
            return verify_moves(words, alive, certificate, budget, max_nodes, stats)
        except CompressedLimit as exc:
            check()
            raise GroupLimit(str(exc)) from exc
    for move in certificate['moves']:
        budget.tick()
        repetitions = 1
        if type(move) is not dict:
            return False
        kind = move.get('kind')
        if kind == 'power_component_delete':
            if certificate['version'] < 10:
                return False
            from .power_component_verify import replay_literal_power_components
            if not replay_literal_power_components(words,alive,move,budget):
                return False
            continue
        if kind == 'power_pair_delete':
            if certificate['version'] < 9:
                return False
            from .power_pair_verify import replay_literal_power_pairs
            if not replay_literal_power_pairs(words,alive,move,budget):
                return False
            continue
        if kind == 'elimination_batch':
            if certificate['version'] < 8:
                return False
            from .elimination_batch_verify import replay_literal_batch
            if not replay_literal_batch(words, alive, move, budget):
                return False
            continue
        if kind == 'primitive_forest':
            if certificate['version'] < 7:
                return False
            from .primitive_forest_verify import replay_literal_forest
            if not replay_literal_forest(words, alive, move, budget):
                return False
            continue
        if kind == 'primitive_projection':
            if certificate['version'] < 6:
                return False
            from .primitive_projection_verify import replay_literal_projection
            if not replay_literal_projection(words, alive, move, budget):
                return False
            continue
        if kind == 'normalize_relators':
            if certificate['version'] < 6 or set(move) != {'kind'}:
                return False
            words = [normalize(word) for word in words]
            continue
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
        elif kind in ('relator', 'relator_power'):
            if certificate['version'] < 2:
                return False
            fields = {'kind', 'target', 'donor', 'target_rotation', 'donor_rotation', 'inverse', 'overlap'}
            if kind == 'relator_power':
                fields.add('copies')
                if (certificate['version'] < 4 or type(move.get('copies')) is not int
                        or move['copies'] < 2):
                    return False
            if set(move) != fields:
                return False
            target, donor = move['target'], move['donor']
            if (type(target) is not int or type(donor) is not int or target == donor
                    or not 0 <= target < len(words) or not 0 <= donor < len(words)
                    or not words[target] or not words[donor]
                    or type(move['inverse']) is not bool):
                return False
            offset, start, overlap = move['target_rotation'], move['donor_rotation'], move['overlap']
            if (type(offset) is not int or not 0 <= offset < len(words[target])
                    or type(start) is not int or not 0 <= start < len(words[donor])
                    or type(overlap) is not int or not 0 < overlap <= min(len(words[target]), len(words[donor]))):
                return False
            # Read both cyclic words via indices, independent of the producer's
            # automaton, rotations and application helper. A donor must remain.
            left = [words[target][(offset+k) % len(words[target])] for k in range(len(words[target]))]
            size = len(words[donor])
            if move['inverse']:
                right = [-words[donor][size-1-(start+k) % size] for k in range(size)]
            else:
                right = [words[donor][(start+k) % size] for k in range(size)]
            budget.tick(len(left)+len(right))
            if kind == 'relator_power':
                copies = move['copies']
                if overlap != size or copies > len(left)//size:
                    return False
                removed = copies*size
                budget.tick(removed)
                if any(left[k] != right[k % size] for k in range(removed)):
                    return False
                words[target] = normalize(left[removed:])
                continue
            if any(left[k] != right[k] for k in range(overlap)):
                return False
            budget.size(sum(map(len, words))+len(right)-2*overlap)
            words[target] = normalize([-right[k] for k in range(len(right)-1, overlap-1, -1)]
                                      + left[overlap:])
            continue
        elif kind in ('whitehead', 'whitehead_power'):
            fields = {'kind', 'multiplier', 'subset'}
            if kind == 'whitehead_power':
                fields.add('exponent')
                if (certificate['version'] < 3 or type(move.get('exponent')) is not int
                        or move['exponent'] < 2):
                    return False
                repetitions = move['exponent']
            if set(move) != fields:
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
        # Independent literal replay of elementary moves, never the producer's
        # run profile or powered images. Reject unaffordable exponents early.
        if repetitions > budget.left:
            budget.tick(repetitions)
        for _ in range(repetitions):
            budget.tick()
            expanded = 0
            for word in words:
                budget.tick(len(word)+1)
                expanded += sum(len(images.get(x, (x,))) for x in word)
            budget.size(expanded)
            words = [normalize(y for x in word for y in images.get(x, (x,))) for word in words]
    budget.tick()
    if certificate['version'] in (6, 7, 8, 9, 10) and certificate['terminal'].get('kind') == 'rank_one_exponent_zero':
        from .primitive_projection_verify import verify_literal_rank_one
        return verify_literal_rank_one(words, alive, certificate['terminal'], budget)
    if certificate['version'] in (5, 6, 7, 8, 9, 10):
        from .primitive_power_verify import verify_literal_terminal
        return verify_literal_terminal(words, alive, certificate['terminal'], budget)
    return alive == {certificate['remaining_generator']} and not any(words)


def group_decide(diagram, *, seconds=0.05, max_letters=200000, max_work=2000000,
                 relator_moves=False, compressed_verification=False,
                 compressed_search=False, adaptive_search=False, switch_letters=None,
                 max_nodes=100000, check=lambda: None, primitive_projection=False, primitive_forest=False, elimination_batch=False):
    """Bounded search AND independent verification sharing one wall allowance.

    primitive_projection opts into raw disjoint-pair rounds and implies
    compressed search/replay. primitive_forest additionally permits acyclic
    unit-coordinate batches and implies projections. Defaults retain the earlier
    search policy. elimination_batch tries general acyclic singleton batches
    with at most max_work//4 total producer work and a 50000-work cap after
    source recovery, then restarts the prior compressed policy on nondecision. Both attempts
    share the producer work allowance and the existing wall deadline.
    """
    from math import isfinite
    start = monotonic()
    if type(compressed_verification) is not bool:
        raise ValueError('compressed_verification must be boolean')
    if type(compressed_search) is not bool:
        raise ValueError('compressed_search must be boolean')
    if type(elimination_batch) is not bool:
        raise ValueError('elimination_batch must be boolean')
    if type(primitive_projection) is not bool:
        raise ValueError('primitive_projection must be boolean')
    if type(primitive_forest) is not bool:
        raise ValueError('primitive_forest must be boolean')
    primitive_projection = primitive_projection or primitive_forest
    compressed_search = compressed_search or primitive_projection or elimination_batch
    if type(adaptive_search) is not bool:
        raise ValueError('adaptive_search must be boolean')
    if compressed_search and adaptive_search:
        raise ValueError('compressed_search and adaptive_search are mutually exclusive')
    if switch_letters is not None and (type(switch_letters) is not int or switch_letters < 0):
        raise ValueError('switch_letters must be a nonnegative integer or None')
    if switch_letters is not None and not adaptive_search:
        raise ValueError('switch_letters requires adaptive search')
    compressed_verification = compressed_verification or compressed_search
    if type(max_nodes) is not int or max_nodes < 0:
        raise ValueError('max_nodes must be a nonnegative integer')
    if seconds is not None and (type(seconds) not in (int, float)
            or not isfinite(seconds) or seconds < 0):
        raise ValueError('group seconds must be finite and nonnegative, or None')
    expires = None if seconds is None else start+seconds

    def tick():
        check()
        if expires is not None and monotonic() >= expires:
            raise GroupLimit('group local time allowance exhausted')

    try:
        search_stats = {}
        search_backend = ('adaptive' if adaptive_search else
                          'compressed-slp' if compressed_search else 'explicit-letters')
        if compressed_search:
            from .compressed_search import compressed_certificate
            if elimination_batch:
                # A different quotient schedule can make later exposure harder.
                # Cap the speculative producer work and reconstruct the original
                # source for the maintained policy when this attempt does not close.
                if type(max_work) is not int or max_work<0:
                    raise ValueError('max_work must be a nonnegative integer')
                probe_stats={};probe_limit=max_work//4;reason=None
                try:
                    certificate = compressed_certificate(diagram, check=tick, max_letters=max_letters,
                        max_work=probe_limit, max_nodes=max_nodes, relator_moves=relator_moves, stats=probe_stats,
                        primitive_projection=primitive_projection, primitive_forest=primitive_forest, elimination_batch=True,
                        post_recovery_work=50000)
                except GroupLimit as exc:
                    tick();certificate=None;reason=str(exc)
                # Recovery failure can precede arena accounting. Once the
                # recovery marker exists, all producer work is accounted for.
                reserve=probe_limit if reason and 'recovery_work' not in probe_stats else 0
                probe_work=max(probe_stats.get('work',0),reserve)
                if certificate is None:
                    search_stats['elimination_fallback']=True
                    search_stats['elimination_probe']=dict(limit=probe_limit,search_limit=50000,charged_work=probe_work,reason=reason,stats=probe_stats)
                    try:
                        certificate = compressed_certificate(diagram, check=tick, max_letters=max_letters,
                            max_work=max(0,max_work-probe_work), max_nodes=max_nodes, relator_moves=relator_moves, stats=search_stats,
                            primitive_projection=primitive_projection, primitive_forest=primitive_forest)
                    finally:search_stats['work']=search_stats.get('work',0)+probe_work
                else:search_stats.update(probe_stats)
                search_stats['elimination_probe']=dict(limit=probe_limit,search_limit=50000,charged_work=probe_work,reason=reason,stats=probe_stats)
            else:
                certificate = compressed_certificate(diagram, check=tick, max_letters=max_letters,
                    max_work=max_work, max_nodes=max_nodes, relator_moves=relator_moves, stats=search_stats,
                    primitive_projection=primitive_projection, primitive_forest=primitive_forest)
        else:
            certificate = group_certificate(diagram, check=tick, max_letters=max_letters, max_work=max_work,
                relator_moves=relator_moves, adaptive=adaptive_search, switch_letters=switch_letters,
                max_nodes=max_nodes, stats=search_stats if adaptive_search else None)
        compressed_verification = compressed_verification or search_stats.get('switched', False)
        if certificate is not None:
            valid = verify_group_certificate(diagram, certificate, check=tick,
                                              max_letters=max_letters, max_work=max_work,
                                              compressed=compressed_verification, max_nodes=max_nodes)
            tick()
            if not valid:
                raise ArithmeticError('produced group certificate failed independent replay')
            return dict(status='UNKNOT', certificate=certificate,
                        search_backend=search_backend,
                        search_stats=search_stats,
                        verification_backend='compressed-slp' if compressed_verification else 'explicit-letters',
                        seconds=monotonic()-start)
        reason = 'group simplification stalled'
    except GroupLimit as exc:
        check()  # A simultaneous global cancellation must still propagate.
        reason = str(exc)
    check()
    return dict(status='INCONCLUSIVE', reason=reason, seconds=monotonic()-start,
                search_backend=search_backend,
                search_stats=search_stats)
