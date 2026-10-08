"""Whole-donor deletion using fully compressed exact substring matching.

This searches the recorded donor spelling and its inverse in a doubled target.
It covers every target rotation, but not all donor rotations or partial overlaps.
Failure is a search stall, never a conclusion about the presented group.
"""
from .compressed_match import first_occurrence


def whole_donor_move(arena, roots):
    nonempty = [(i, root) for i, root in enumerate(roots) if root]
    arena.tick(len(roots)+1)
    # Descending donor size maximizes the guaranteed gain among whole-donor
    # deletions found by this restricted search. Per-root counts prune pairs.
    donors = sorted(nonempty, key=lambda item: (-arena.lengths[item[1]], item[0]))
    counts = {i: arena.summarize([root])[0] for i, root in nonempty}
    doubled = {}
    for donor, source in donors:
        size = arena.lengths[source]
        for inverse in (False, True):
            pattern = arena.inverse(source) if inverse else source
            for target, other in nonempty:
                arena.tick(len(counts[donor])+1)
                if (target == donor or arena.lengths[other] < size
                        or any(counts[target].get(g, 0) < count for g, count in counts[donor].items())):
                    continue
                if target not in doubled:
                    doubled[target] = arena.concat(other, other)
                position = first_occurrence(arena, pattern, doubled[target])
                if position is not None:
                    return dict(kind='relator', target=target, donor=donor,
                        target_rotation=position % arena.lengths[other], donor_rotation=0,
                        inverse=inverse, overlap=size)
    return None


def apply_whole_donor(arena, roots, move):
    """Producer application; the existing independent verifiers check replay."""
    target, donor = move['target'], move['donor']
    size = arena.lengths[roots[target]]
    offset, overlap = move['target_rotation'], move['overlap']
    rotated = arena.concat(arena.slice(roots[target], offset, size),
                           arena.slice(roots[target], 0, offset))
    pattern = arena.inverse(roots[donor]) if move['inverse'] else roots[donor]
    if overlap != arena.lengths[pattern] or arena.lcp(pattern, rotated) != overlap:
        raise ArithmeticError('compressed donor match failed exact prefix replay')
    roots[target] = arena.cyclic_reduce(arena.slice(rotated, overlap, size))
