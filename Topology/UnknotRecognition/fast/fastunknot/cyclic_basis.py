"""Compressed certificates for a common basis of cyclic boundary words.

This is an algebraic component, not a knot or handlebody recognizer.  A caller
must authenticate the embedded curves and their marking before using Gordon's
primitive-multicurve theorem.  The producer is complete when each connected
component of the cyclically reduced generator-support graph has size at most
two.  Larger components are a method refusal, never a nonprimitivity claim.

The rank-two singleton algorithm is the Euclidean method of Kapovich (2026).
Pairs use one lift of their inverse homology matrix.  Supplied powered Nielsen
certificates are replayed backwards, retaining a linear shared grammar before
the established deterministic compressed free reduction.
"""

from .compressed_words import CompressedLimit, WordArena


def concatenate(arena, nodes):
    """Join node references in a balanced tree, without free reduction."""
    nodes = list(nodes)
    while len(nodes) > 1:
        nodes = [arena.concat(nodes[i], nodes[i + 1]) if i + 1 < len(nodes)
                 else nodes[i] for i in range(0, len(nodes), 2)]
    arena.tick()
    return nodes[0] if nodes else 0


def map_unreduced(arena, roots, images):
    """Apply a supplied letter map once; preserve shared source productions."""
    mapped = {0: 0}
    for node in arena._reachable(roots):
        rule = arena.rules[node]
        if rule[0] == 't':
            mapped[node] = images[rule[1]]
        else:
            mapped[node] = arena.concat(mapped[rule[1]], mapped[rule[2]])
    return [mapped[root] for root in roots]


def _labels(generators):
    if (type(generators) is not list or
            any(type(g) is not int or g <= 0 for g in generators) or
            generators != sorted(set(generators))):
        raise ValueError('generators must be sorted distinct positive integers')
    return set(generators)


def compile_nielsen(arena, generators, moves):
    """Compile psi_m ... psi_1 by suffix images, scanning the list backwards.

    Moves are inversion, interchange, and x_i -> x_j^k x_i or x_i x_j^k,
    with i != j and binary k != 0.  No group simplification is needed here.
    """
    alive = _labels(generators)
    if type(moves) is not list:
        raise ValueError('moves must be a list')
    images = {g: arena.letter(g) for g in generators}
    for move in reversed(moves):
        arena.tick()
        if type(move) is not dict:
            raise ValueError('invalid Nielsen move')
        kind = move.get('kind')
        if kind == 'invert':
            if set(move) != {'kind', 'generator'}:
                raise ValueError('invalid inversion fields')
            i = move['generator']
            if type(i) is not int or i not in alive:
                raise ValueError('inversion outside alphabet')
            images[i] = arena.inverse(images[i])
        elif kind == 'swap':
            if set(move) != {'kind', 'first', 'second'}:
                raise ValueError('invalid interchange fields')
            i, j = move['first'], move['second']
            if (type(i) is not int or type(j) is not int or
                    i not in alive or j not in alive or i == j):
                raise ValueError('invalid interchange generators')
            images[i], images[j] = images[j], images[i]
        elif kind == 'multiply':
            if set(move) != {'kind', 'target', 'donor', 'exponent', 'side'}:
                raise ValueError('invalid multiplication fields')
            i, j, k = move['target'], move['donor'], move['exponent']
            if (type(i) is not int or type(j) is not int or i == j or
                    i not in alive or j not in alive or type(k) is not int or
                    k == 0 or move['side'] not in ('left', 'right')):
                raise ValueError('invalid powered Nielsen multiplication')
            power = arena.power(images[j], k)
            images[i] = (arena.concat(power, images[i]) if move['side'] == 'left'
                         else arena.concat(images[i], power))
        else:
            raise ValueError('unknown Nielsen move')
    images.update({-g: arena.inverse(images[g]) for g in generators})
    return images


def _profiles(arena, roots):
    """Exact signed exponent sums and signed support, per reachable node."""
    sums, support = {0: {}}, {0: frozenset()}
    for node in arena._reachable(roots):
        arena.tick()
        rule = arena.rules[node]
        if rule[0] == 't':
            letter = rule[1]
            sums[node] = {abs(letter): 1 if letter > 0 else -1}
            support[node] = frozenset((abs(letter),))
        else:
            a, b = rule[1:]
            row = dict(sums[a])
            for g, n in sums[b].items():
                row[g] = row.get(g, 0) + n
            sums[node] = row
            support[node] = support[a] | support[b]
    return [sums[x] for x in roots], [support[x] for x in roots]


def rank_two_lift(labels, vectors):
    """Lift inverse homology data for one or two ordered classes in F_2.

    Return (moves, target letters), or None for the homological obstruction.
    Completeness is a statement about primitive CONJUGACY classes, not based
    generating pairs: independent conjugations are intentionally allowed.
    """
    from math import gcd
    a, b = labels
    if len(vectors) not in (1, 2):
        return None
    values = [list(v) for v in vectors]
    p, q = values[0]
    if gcd(abs(p), abs(q)) != 1:
        return None
    if len(values) == 2 and abs(p * values[1][1] - q * values[1][0]) != 1:
        return None
    moves = []

    def invert(column):
        moves.append(dict(kind='invert', generator=(a, b)[column]))
        for value in values:
            value[column] = -value[column]

    def shear(target, donor, exponent):
        # x_target -> x_donor^exponent x_target adds target counts to donor.
        moves.append(dict(kind='multiply', target=(a, b)[target],
                          donor=(a, b)[donor], exponent=exponent, side='left'))
        for value in values:
            value[donor] += exponent * value[target]

    if values[0][0] < 0:
        invert(0)
    if values[0][1] < 0:
        invert(1)
    while all(values[0]):
        p, q = values[0]
        if p >= q:
            shear(1, 0, -(p // q))
        else:
            shear(0, 1, -(q // p))
    if values[0][0] == 0:
        moves.append(dict(kind='swap', first=a, second=b))
        values = [[y, x] for x, y in values]
    if values[0] != [1, 0]:
        raise ArithmeticError('Euclidean lift did not reach a primitive vector')
    if len(values) == 2:
        p, q = values[1]
        if abs(q) != 1:
            raise ArithmeticError('unimodular pair lost its determinant')
        if p:
            shear(1, 0, -p * q)
        if values[1][1] < 0:
            invert(1)
        if values[1] != [0, 1]:
            raise ArithmeticError('pair lift failed')
    return moves, [a, b][:len(values)]


def cyclic_basis_blocks(arena, roots, generators):
    """Find a common basis certificate for support blocks of size at most two.

    A negative result has a reason.  'unsupported_support_block' is outside
    the exact restricted class; the other failures certify algebraic
    nonprimitivity within a supported block, not non-handlebodyness.
    """
    alive = _labels(generators)
    for node in arena._reachable(roots):
        rule = arena.rules[node]
        if rule[0] == 't' and abs(rule[1]) not in alive:
            raise ValueError('source word outside component alphabet')
    reduced = [arena.cyclic_reduce(root) for root in roots]
    if any(not root for root in reduced):
        return dict(status='INCONCLUSIVE', reason='trivial_annular_class')
    sums, support = _profiles(arena, reduced)
    if any(not s <= alive for s in support):
        raise ValueError('word outside component alphabet')
    parent = {g: g for g in generators}

    def find(g):
        while parent[g] != g:
            parent[g] = parent[parent[g]]
            g = parent[g]
        return g

    for letters in support:
        letters = sorted(letters)
        for g in letters[1:]:
            parent[find(g)] = find(letters[0])
    groups = {}
    for slot, letters in enumerate(support):
        key = find(min(letters))
        groups.setdefault(key, []).append(slot)
    moves, targets, blocks = [], [None] * len(roots), []
    for key, slots in sorted(groups.items()):
        labels = sorted(set().union(*(support[i] for i in slots)))
        if len(labels) > 2:
            return dict(status='INCONCLUSIVE', reason='unsupported_support_block',
                        block_generators=labels)
        if len(slots) > len(labels):
            return dict(status='INCONCLUSIVE', reason='dependent_annular_classes',
                        block_generators=labels)
        local_moves = []
        if len(labels) == 1:
            g = labels[0]
            value = sums[slots[0]].get(g, 0)
            if abs(value) != 1:
                return dict(status='INCONCLUSIVE', reason='nonprimitive_homology')
            if value < 0:
                local_moves.append(dict(kind='invert', generator=g))
            local_targets = [g]
        else:
            vectors = [[sums[i].get(g, 0) for g in labels] for i in slots]
            lift = rank_two_lift(labels, vectors)
            if lift is None:
                return dict(status='INCONCLUSIVE', reason='nonprimitive_homology')
            local_moves, local_targets = lift
        moves.extend(local_moves)
        for i, target in zip(slots, local_targets):
            targets[i] = target
        blocks.append(dict(generators=labels, slots=slots))
    images = compile_nielsen(arena, generators, moves)
    mapped = map_unreduced(arena, reduced, images)
    terminal = [arena.cyclic_reduce(root) for root in mapped]
    if any(arena.lengths[root] != 1 or arena.first[root] != target
           for root, target in zip(terminal, targets)):
        return dict(status='INCONCLUSIVE', reason='nonprimitive_cyclic_class')
    certificate = dict(schema='cyclic-basis-nielsen-v1', generators=generators,
                       moves=moves, targets=targets)
    return dict(status='COMPLETE', certificate=certificate, blocks=blocks,
                stats=dict(nielsen_moves=len(moves), blocks=len(blocks),
                           maximum_block=max((len(b['generators']) for b in blocks), default=0)))


def literal_cyclic_basis(words, generators, *, max_nodes=1000000, max_work=10000000):
    """Convenience entry point for experiments; all decision paths stay exact."""
    arena = WordArena(max_nodes=max_nodes, max_work=max_work)
    try:
        roots = [arena.from_word(word) for word in words]
        result = cyclic_basis_blocks(arena, roots, generators)
        result['arena_stats'] = dict(arena.stats, grammar_nodes=len(arena.rules) - 1)
        return result
    except CompressedLimit as error:
        return dict(status='INCONCLUSIVE', reason='compressed_word_budget', detail=str(error))
