"""Whole-donor deletion using fully compressed exact substring matching.

This searches the recorded donor spelling and its inverse in a doubled target.
It covers every target rotation, but not all donor rotations or partial overlaps.
Failure is a search stall, never a conclusion about the presented group.
"""
from .compressed_match import first_occurrence


def whole_donor_move(arena, roots):
    nonempty = [(i, root) for i, root in enumerate(roots) if root]
    arena.tick(len(roots)+1)
    # Prioritize longer donors, then batch consecutive copies at the chosen
    # occurrence. This does not maximize gain over every possible overlap.
    donors = sorted(nonempty, key=lambda item: (-arena.lengths[item[1]], item[0]))
    counts = {i: arena.summarize([root])[0] for i, root in nonempty}
    doubled = {}
    for donor, source in donors:
        size = arena.lengths[source]
        eligible = []
        for target, other in nonempty:
            arena.tick(len(counts[donor])+1)
            if (target != donor and arena.lengths[other] >= size
                    and all(counts[target].get(g, 0) >= count for g, count in counts[donor].items())):
                eligible.append((target, other))
        if not eligible:
            continue
        for inverse in (False, True):
            pattern = arena.inverse(source) if inverse else source
            for target, other in eligible:
                arena.tick()
                if target not in doubled:
                    doubled[target] = arena.concat(other, other)
                position = first_occurrence(arena, pattern, doubled[target])
                if position is not None:
                    length = arena.lengths[other]
                    offset = position % length
                    move = dict(kind='relator', target=target, donor=donor,
                        target_rotation=offset, donor_rotation=0,
                        inverse=inverse, overlap=size)
                    capacity = length//size
                    if capacity > 1:
                        rotated = arena.concat(arena.slice(other, offset, length), arena.slice(other, 0, offset))
                        copies = arena.lcp(rotated, arena.power(pattern, capacity))//size
                        if copies > 1:
                            move.update(kind='relator_power', copies=copies)
                    return move
    return None


def apply_whole_donor(arena, roots, move):
    """Producer application; the existing independent verifiers check replay."""
    target, donor = move['target'], move['donor']
    size = arena.lengths[roots[target]]
    offset, overlap = move['target_rotation'], move['overlap']
    rotated = arena.concat(arena.slice(roots[target], offset, size),
                           arena.slice(roots[target], 0, offset))
    pattern = arena.inverse(roots[donor]) if move['inverse'] else roots[donor]
    copies = move.get('copies', 1)
    removed = copies*overlap
    repeated = arena.power(pattern, copies) if copies > 1 else pattern
    if overlap != arena.lengths[pattern] or removed > size or arena.lcp(repeated, rotated) != removed:
        raise ArithmeticError('compressed donor match failed exact prefix replay')
    roots[target] = arena.cyclic_reduce(arena.slice(rotated, removed, size))
    if copies > 1:
        arena.stats['relator_power_moves'] = arena.stats.get('relator_power_moves', 0)+1
        arena.stats['max_relator_power_bits'] = max(arena.stats.get('max_relator_power_bits', 0), copies.bit_length())
