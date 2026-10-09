"""Optional SLP search with complete strictly shortening cyclic overlap queries.

Only the wrapper reconstructs a knot presentation. Internal search success is
not a knot verdict: group_decide independently rebuilds and checks the trace.
Individual compressed operations do not bound search length or grammar growth.
"""
from .compressed_words import WordArena, CompressedLimit
from .group_certificate import _Budget, _presentation, _whitehead_cut, _image, _reduce, _certificate_version, GroupLimit
from .whitehead_power import power_profile, powered_images


def _search(arena, roots, alive, moves, *, relator_moves=False, max_letters=200000,
            primitive_terminal=None, primitive_projection=False, rank_two_terminal=True, primitive_forest=False, elimination_batch=False):
    """Return algebraic success; an optional output dict enables the new terminal.

    Without that dict, True retains the old rank-one, no-relator contract.
    With it, evidence may instead record an intact rank-two state or a raw
    one-generator zero-exponent endpoint after disjoint projections. Only a
    source-reconstructing wrapper can turn this into a verdict.
    """
    primitive_projection = primitive_projection or primitive_forest
    if (primitive_projection or elimination_batch) and primitive_terminal is None:
        raise ValueError('raw batch search requires an explicit terminal output')
    raw = False
    normalization_cache = {} if primitive_projection or elimination_batch else None
    elimination_cache = {} if elimination_batch else None
    projection_cache = {} if primitive_projection else None
    while len(alive) > 1:
        if rank_two_terminal and primitive_terminal is not None and len(alive) == 2:
            from .primitive_power import primitive_power_terminal
            evidence = primitive_power_terminal(arena, roots, alive)
            if evidence is not None:
                primitive_terminal.update(evidence)
                return True

        if elimination_batch and len(alive) >= 3:
            from .elimination_batch import plan_batch, apply_batch
            selected = plan_batch(arena, roots, alive, elimination_cache, ordered=True)
            if len(selected) >= 2:
                apply_batch(arena, roots, alive, selected)
                moves.append(dict(kind='elimination_batch', entries=selected))
                raw = True
                continue

        if primitive_projection:
            from .primitive_projection import projection_candidates, plan_projection, apply_projection
            prepared = projection_candidates(arena, roots, alive, projection_cache)
            if primitive_forest and len(prepared[0]) >= 2:
                from .primitive_forest import plan_forest, apply_forest
                edges = plan_forest(arena, roots, alive, projection_cache, _prepared=prepared)
                if len(edges) >= 2:
                    apply_forest(arena, roots, alive, edges)
                    moves.append(dict(kind='primitive_forest', edges=edges))
                    raw = True
                    continue
            elif primitive_forest:
                # Two edges need two current donor slots. Skip graph setup;
                # this bound is exact, not a heuristic suspension of discovery.
                arena.stats['forest_candidate_skips'] = arena.stats.get('forest_candidate_skips',0)+1
            selected = plan_projection(arena, roots, alive, projection_cache, _prepared=prepared)
            if selected:
                apply_projection(arena, roots, alive, selected)
                moves.append(dict(kind='primitive_projection', pairs=selected))
                raw = True
                continue
        if raw:
            # The old positional moves operate on cyclically reduced roots.
            # Record this boundary explicitly so both replayers use that state.
            from .syllable_normalize import bounded_cyclic_roots
            normalized = bounded_cyclic_roots(arena, roots, cache=normalization_cache)
            roots[:] = normalized if normalized is not None else [arena.cyclic_reduce(x) for x in roots]
            moves.append(dict(kind='normalize_relators'))
            normalization_stat = 'elimination_normalizations' if elimination_batch else 'projection_normalizations'
            arena.stats[normalization_stat] = arena.stats.get(normalization_stat,0)+1
            raw = False
            continue

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
                    from .compressed_overlap import cyclic_overlap_move, apply_cyclic_overlap
                    arena.stats['compressed_lcs_attempts'] = arena.stats.get('compressed_lcs_attempts', 0)+1
                    move = cyclic_overlap_move(arena, roots)
                    if move is not None:
                        apply_cyclic_overlap(arena, roots, move)
                        moves.append(move)
                        arena.stats['compressed_lcs_moves'] = arena.stats.get('compressed_lcs_moves', 0)+1
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
    if raw:
        from .primitive_projection import rank_one_zero
        if rank_one_zero(arena, roots, alive):
            primitive_terminal.update(kind='rank_one_exponent_zero',generator=next(iter(alive)))
            return True
        return False
    return len(alive) == 1 and not any(roots)


def compressed_certificate(diagram, *, check=lambda: None, max_letters=200000,
                           max_work=2000000, max_nodes=100000, relator_moves=False, stats=None,
                           primitive_power=True, primitive_projection=False, primitive_forest=False, elimination_batch=False,
                           post_recovery_work=None):
    """Find a trace or None; resource exhaustion raises GroupLimit.

    max_letters caps the initial presentation and optional overlap expansion.
    All elimination and Whitehead operations instead obey max_nodes/max_work.
    The initial PD is always reconstructed; no caller-supplied state is trusted.
    primitive_power tries report 45's arithmetic rank-two terminal before
    general elimination/shortening and emits version five on a local hit;
    independent source-bound replay is still required before trusting it.
    Disjoint primitive projections run on raw circuits with an explicit
    normalization handoff. Version six replays each full projection round.
    primitive_forest additionally batches overlapping unit-coordinate donors
    with acyclic dependencies and emits version seven on activation. It implies
    primitive_projection; both modes are optional.
    elimination_batch separately enables acyclic singleton definitions with
    arbitrary word images and emits version eight on activation.
    post_recovery_work optionally limits producer work after rebuilding the
    source presentation; max_work still caps recovery and search together.
    Disable both projection options to retain the version-five search; disabling
    both primitive options retains the historical rank-one contract.
    """
    if type(elimination_batch) is not bool:
        raise ValueError('elimination_batch must be boolean')
    if post_recovery_work is not None and (type(post_recovery_work) is not int or post_recovery_work < 0):
        raise ValueError('post_recovery_work must be a nonnegative integer or None')
    if type(primitive_projection) is not bool:
        raise ValueError('primitive_projection must be boolean')
    if type(primitive_forest) is not bool:
        raise ValueError('primitive_forest must be boolean')
    primitive_projection = primitive_projection or primitive_forest
    if type(primitive_power) is not bool:
        raise ValueError('primitive_power must be boolean')
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
        if post_recovery_work is not None:
            arena.stats['recovery_work'] = arena.stats['work']
            arena.left = min(arena.left, post_recovery_work)
            arena.stats['post_recovery_limit'] = arena.left
        moves = []
        terminal = {} if primitive_power or primitive_projection or elimination_batch else None
        if not _search(arena, roots, alive, moves, relator_moves=relator_moves, max_letters=max_letters,
                       primitive_terminal=terminal, primitive_projection=primitive_projection,
                       rank_two_terminal=primitive_power, primitive_forest=primitive_forest, elimination_batch=elimination_batch):
            return None
        batched = any(move['kind'] == 'elimination_batch' for move in moves)
        forested = any(move['kind'] == 'primitive_forest' for move in moves)
        projected = batched or forested or any(move['kind'] == 'primitive_projection' for move in moves)
        if projected and not terminal:
            terminal.update(kind='rank_one_exponent_zero',generator=next(iter(alive)))
        if terminal:
            return dict(version=8 if batched else 7 if forested else 6 if projected else 5, method='wirtinger-cyclic-group', status='UNKNOT',
                        input_pd=[list(row) for row in diagram.pd], moves=moves, terminal=terminal)
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
