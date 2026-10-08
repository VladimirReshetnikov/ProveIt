"""Optional SLP search with explicit overlaps and compressed donor deletion.

Only the wrapper reconstructs a knot presentation. Internal search success is
not a knot verdict: group_decide independently rebuilds and checks the trace.
Individual compressed operations do not bound search length or grammar growth.
"""
from .compressed_words import WordArena, CompressedLimit
from .group_certificate import _Budget, _presentation, _whitehead_cut, _image, _reduce, _certificate_version, GroupLimit
from .whitehead_power import power_profile, powered_images


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
                # Keep ordinary shortening paths cheap. When they would stall,
                # search for whole donors without expanding either relator.
                if cut is None:
                    cut = whitehead()
                if cut[0] >= 0:
                    from .compressed_overlap import whole_donor_move, apply_whole_donor
                    arena.stats['compressed_overlap_attempts'] = arena.stats.get('compressed_overlap_attempts', 0)+1
                    move = whole_donor_move(arena, roots)
                    if move is not None:
                        apply_whole_donor(arena, roots, move)
                        arena.stats['compressed_overlap_moves'] = arena.stats.get('compressed_overlap_moves', 0)+1
                        moves.append(move)
                        continue
        if cut is None:
            cut = whitehead()
        change, a, subset = cut
        if change >= 0:
            return False
        before = sum(arena.lengths[x] for x in roots)
        previous = moves[-1] if moves else {}
        repeated = (previous.get('kind') in ('whitehead', 'whitehead_power')
                    and previous['multiplier'] == a and set(previous['subset']) == subset)
        exponent, gain = 1, change
        # Small incompressible states rarely benefit from scanning a gap
        # profile. Repetition or large expansion justifies that extra work.
        if repeated or before > 4*len(arena.rules):
            arena.stats['power_profiles'] = arena.stats.get('power_profiles', 0)+1
            exponent, gain, unit = power_profile(arena, roots, a, subset)
            if unit != change or exponent < 1 or gain > change:
                raise ArithmeticError('Whitehead cut and power profile disagree')
        if exponent == 1:
            images = {x: arena.from_word(_image(x, a, subset))
                      for g in alive for x in (g, -g)}
        else:
            images = powered_images(arena, alive, a, subset, exponent)
        roots[:] = [arena.cyclic_reduce(x) for x in arena.substitute(roots, images)]
        if sum(arena.lengths[x] for x in roots)-before != gain:
            raise ArithmeticError('Whitehead power and compressed substitution disagree')
        move = dict(kind='whitehead', multiplier=a, subset=sorted(subset))
        if exponent > 1:
            move.update(kind='whitehead_power', exponent=exponent)
            arena.stats['power_moves'] = arena.stats.get('power_moves', 0)+1
            arena.stats['max_power_bits'] = max(arena.stats.get('max_power_bits', 0), exponent.bit_length())
        moves.append(move)
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
        return dict(version=_certificate_version(moves),
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


def _continue_compressed(words, alive, moves, budget, max_nodes, relator_moves, stats):
    """Internal handoff from an intact explicit state; never a verdict API.

    Preserve relator slots, generator names and the existing trace. Conversion
    and continuation consume the remainder of the original search allowance.
    """
    arena = WordArena(max_nodes=max_nodes, max_work=budget.left, check=budget.check)
    try:
        roots = [arena.reduce(arena.from_word(word)) for word in words]
        return _search(arena, roots, alive, moves, relator_moves=relator_moves,
                       max_letters=budget.max_letters)
    except CompressedLimit as exc:
        budget.check()
        raise GroupLimit(str(exc)) from exc
    finally:
        budget.left = arena.left
        if stats is not None:
            stats['compressed'] = dict(arena.stats, nodes=len(arena.rules)-1,
                                       largest_word_bits=max(arena.lengths).bit_length())
