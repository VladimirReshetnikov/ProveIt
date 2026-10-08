"""Optional SLP elimination/Whitehead search with bounded explicit overlaps.

Only the wrapper reconstructs a knot presentation. Internal search success is
not a knot verdict: group_decide independently rebuilds and checks the trace.
Individual compressed operations do not bound search length or grammar growth.
"""
from .compressed_words import WordArena, CompressedLimit
from .group_certificate import _Budget, _presentation, _whitehead_cut, _image, _reduce, GroupLimit


def _search(arena, roots, alive, moves, *, relator_moves=False, max_letters=200000):
    while len(alive) > 1:
        counts, _ = arena.summarize(roots)
        candidates = []
        for i, local in enumerate(arena.singletons(roots)):
            arena.tick(len(local)+1)
            length = arena.lengths[roots[i]]
            candidates.extend(((length-2)*counts[g], length, i, g)
                              for g in local)
        if candidates:
            _, _, index, g = min(candidates)
            root = roots[index]
            _, position, signed = arena.occurrence(root, g)
            rest = arena.concat(arena.slice(root, position+1, arena.lengths[root]),
                                arena.slice(root, 0, position))
            value = arena.reduce(arena.inverse(rest) if signed > 0 else rest)
            roots[index] = 0
            roots[:] = [arena.cyclic_reduce(x) for x in arena.substitute(
                roots, {g: value, -g: arena.inverse(value)})]
            alive.remove(g)
            moves.append(dict(kind='eliminate', relation=index, generator=g))
            continue

        def whitehead():
            _, graph = arena.summarize(roots, whitehead=True)
            return _whitehead_cut(graph, arena)

        cut = whitehead() if not relator_moves or len(alive) <= 6 else None
        if relator_moves and (cut is None or cut[0] >= 0):
            length = sum(arena.lengths[x] for x in roots)
            arena.tick(len(roots)+1)
            if length <= max_letters:
                # Expansion occurs only in this explicitly bounded bridge.
                # Deduct its suffix-automaton work from the same search budget.
                from .relator_overlap import overlap_move, apply_overlap
                words = [arena.expand(x, limit=max_letters) for x in roots]
                budget = _Budget(arena.check, max_letters, arena.left)
                try:
                    move = overlap_move(words, budget)
                    if move is not None:
                        apply_overlap(words, move, budget, _reduce)
                finally:
                    arena.tick(arena.left-budget.left)
                arena.stats['overlap_expansions'] = arena.stats.get('overlap_expansions', 0)+1
                if move is not None:
                    roots[:] = [arena.reduce(arena.from_word(w)) for w in words]
                    moves.append(move)
                    continue
            else:
                arena.stats['overlap_skips'] = arena.stats.get('overlap_skips', 0)+1
        if cut is None:
            cut = whitehead()
        change, a, subset = cut
        if change >= 0:
            return False
        before = sum(arena.lengths[x] for x in roots)
        images = {x: arena.from_word(_image(x, a, subset))
                  for g in alive for x in (g, -g)}
        roots[:] = [arena.cyclic_reduce(x) for x in arena.substitute(roots, images)]
        if sum(arena.lengths[x] for x in roots)-before != change:
            raise ArithmeticError('Whitehead cut and compressed substitution disagree')
        moves.append(dict(kind='whitehead', multiplier=a, subset=sorted(subset)))
    arena.tick()
    return len(alive) == 1 and not any(roots)


def compressed_certificate(diagram, *, check=lambda: None, max_letters=200000,
                           max_work=2000000, max_nodes=100000, relator_moves=False, stats=None):
    """Find a trace or None; resource exhaustion raises GroupLimit.

    max_letters caps the initial presentation and optional overlap expansion.
    All elimination and Whitehead operations instead obey max_nodes/max_work.
    The initial PD is always reconstructed; no caller-supplied state is trusted.
    """
    if type(relator_moves) is not bool:
        raise ValueError('relator_moves must be boolean')
    if stats is not None and type(stats) is not dict:
        raise ValueError('stats must be a dictionary or None')
    budget = _Budget(check, max_letters, max_work)
    arena = WordArena(max_nodes=max_nodes, max_work=max_work, check=check)
    try:
        alive, words = _presentation(diagram, budget)
        arena.tick(max_work-budget.left)
        roots = [arena.reduce(arena.from_word(word)) for word in words]
        moves = []
        if not _search(arena, roots, alive, moves, relator_moves=relator_moves, max_letters=max_letters):
            return None
        return dict(version=2 if any(m['kind'] == 'relator' for m in moves) else 1,
                    method='wirtinger-cyclic-group', status='UNKNOT',
                    input_pd=[list(row) for row in diagram.pd], moves=moves,
                    remaining_generator=next(iter(alive)))
    except CompressedLimit as exc:
        check()
        raise GroupLimit(str(exc)) from exc
    finally:
        if stats is not None:
            stats.update(arena.stats, nodes=len(arena.rules)-1,
                         largest_word_bits=max(arena.lengths).bit_length())
