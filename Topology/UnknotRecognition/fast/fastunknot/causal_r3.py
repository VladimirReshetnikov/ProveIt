"""Bounded RIII search with accumulated support (research report 27).

Births are pairwise footprint-disjoint moves, placed first in canonical order.
Subsequent moves meet the accumulated support. An immediate inverse is pruned
only when the preceding move added no support: restoring the diagram alone
need not restore the support or the birth budget.
An explicit DFS stack avoids recursion limits and exponential memo storage.
"""


def footprint(state, triangle):
    local = {4 * (d // 4) + j for d in triangle for j in range(4)}
    return frozenset(local | {state.alpha[d] for d in local})


def _triangles(state, darts, check):
    seen = set()
    for d in darts:
        if check is not None:
            check()
        triangle = state.triangle_at(d)
        if triangle is None:
            continue
        key = tuple(sorted(triangle))
        if key not in seen:
            seen.add(key)
            yield key, triangle


def _candidates(state, active, births, birth_phase, last_key, max_births, check):
    if birth_phase and births < max_births:
        for key, triangle in _triangles(state, range(4 * len(state.alive)), check):
            if last_key is not None and key <= last_key:
                continue
            support = footprint(state, triangle)
            if active.isdisjoint(support):
                yield triangle, support, births + 1, True, key
    if active:
        crossings = set()
        for d in active:
            if check is not None:
                check()
            crossings.update((d // 4, state.alpha[d] // 4))
        darts = (4 * c + j for c in sorted(crossings) for j in range(4))
        for _, triangle in _triangles(state, darts, check):
            support = footprint(state, triangle)
            if not active.isdisjoint(support):
                yield triangle, support, births, False, last_key


def search_clustered_unlock(state, depth, *, max_births=1, check_faces=True,
                            path=None, check=None):
    """Leave a successful path applied; restore alpha/path on failure or error.

    The caller supplies ``state.trials`` and ``state.budget`` and exhausts RI/II
    first. With enough trials the search is complete within the supplied depth
    and birth bounds. Trial exhaustion is inconclusive. Counters are not undone.
    """
    if type(depth) is not int or depth < 1:
        raise ValueError("depth must be a positive integer")
    if type(max_births) is not int or max_births < 1:
        raise ValueError("max_births must be a positive integer")
    if path is None:
        path = []
    # Each nonroot frame owns the pre-move pairing entries and one path entry.
    # Register the journal before mutation, including a degenerate/raising trial.
    frames = [(_candidates(state, frozenset(), 0, True, None, max_births, check),
               frozenset(), depth, None, None)]
    keep = False

    def restore_frame():
        _, _, _, saved, _ = frames.pop()
        for d, partner in saved:
            state.alpha[d] = partner
        path.pop()

    try:
        while frames:
            if check is not None:
                check()
            if state.trials >= state.budget:
                return None
            candidates, active, remaining, _, inverse = frames[-1]
            candidate = next(candidates, None)
            if candidate is None:
                if len(frames) == 1:
                    return None
                restore_frame()
                continue
            triangle, support, births, birth_phase, last_key = candidate
            if inverse is not None and tuple(sorted(triangle)) == inverse:
                continue
            if remaining == 1 and check_faces and not state.r3_can_help(triangle):
                continue
            new_active = active | support
            children = (_candidates(state, new_active, births, birth_phase,
                                    last_key, max_births, check)
                        if remaining > 1 else iter(()))
            saved = [(d, state.alpha[d]) for d in support]
            # Deleting this move followed by its inverse preserves both state
            # and accumulated support only if the move added no new sites.
            # Birth count/key are then unchanged, and remaining connected moves
            # are still available even if deleting the pair delays that phase.
            inverse = tuple(sorted(d ^ 2 for d in triangle)) if support <= active else None
            frames.append((children, new_active, remaining - 1, saved, inverse))
            path.append(triangle)
            if state.apply_r3(triangle) is None:
                restore_frame()
                continue
            state.trials += 1
            around = [4 * c + j for c in sorted({d // 4 for d in support})
                      for j in range(4)]
            for d in around:
                if check is not None:
                    check()
                if state.move_at(d) is not None:
                    keep = True
                    return around
    finally:
        if not keep:
            while len(frames) > 1:
                restore_frame()
    return None
