"""Exact compressed relator overlaps with a cheap whole-donor first stage.

The complete fallback searches all cyclic rotations and partial overlaps.
Failure is a search stall, never a conclusion about the presented group.
"""
from .compressed_match import first_occurrence
from .compressed_lcs import adjacent_pairs
from .compressed_words import CompressedLimit


def whole_donor_move(arena, roots):
    nonempty = [(i, root) for i, root in enumerate(roots) if root]
    arena.tick(len(roots)+1)
    # Prioritize longer donors, then batch consecutive copies at the chosen
    # occurrence. This does not maximize gain over every possible overlap.
    donors = sorted(nonempty, key=lambda item: (-arena.lengths[item[1]], item[0]))
    counts = {i: arena.summarize([root])[0] for i, root in nonempty}
    doubled, pairs, pair_cells = {}, {}, 0
    uniform = getattr(arena, 'uniform', None)

    def internal_pairs(root):
        nonlocal pair_cells
        if root not in pairs:
            letter = uniform[root] if uniform is not None else 0
            if letter:
                arena.tick()
                found = {(letter, letter)} if arena.lengths[root] > 1 else set()
            else:
                found = adjacent_pairs(arena, arena._reachable([root]))
            pair_cells += len(found)+1
            if pair_cells > arena.max_nodes:
                raise CompressedLimit('compressed-overlap adjacency cache allowance exhausted')
            pairs[root] = found
        return pairs[root]

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
        source_pairs = internal_pairs(source)
        for inverse in (False, True):
            arena.tick(len(source_pairs)+1)
            required = {(-y, -x) for x, y in source_pairs} if inverse else source_pairs
            compatible = []
            for target, other in eligible:
                arena.tick(len(required)+1)
                available = internal_pairs(other) | {(arena.last[other], arena.first[other])}
                if required <= available:
                    compatible.append((target, other))
                else:
                    arena.stats['overlap_adjacency_skips'] = arena.stats.get('overlap_adjacency_skips', 0)+1
            if not compatible:
                continue
            pattern = arena.inverse(source) if inverse else source
            for target, other in compatible:
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


def cyclic_overlap_move(arena, roots):
    """Find a strictly shortening overlap over all rotations and both signs.

    Searching the shorter donor of each unordered pair suffices for existence:
    it offers at least the gain of using the longer relation as donor.
    """
    from .compressed_lcs import CommonSubstring
    nonempty = sorted(((i, root) for i, root in enumerate(roots) if root),
                      key=lambda item: (arena.lengths[item[1]], item[0]))
    counts = {i: arena.summarize([root])[0] for i, root in nonempty}
    matcher, doubled = CommonSubstring(arena), {}
    for index, (donor, source) in enumerate(nonempty):
        size = arena.lengths[source]
        for target, other in nonempty[index+1:]:
            arena.tick(len(counts[donor])+1)
            shared = sum(min(n, counts[target].get(g, 0)) for g, n in counts[donor].items())
            if 2*shared <= size:
                continue
            if other not in doubled:
                doubled[other] = arena.concat(other, other)
            for inverse in (False, True):
                pattern = arena.inverse(source) if inverse else source
                if pattern not in doubled:
                    doubled[pattern] = arena.concat(pattern, pattern)
                overlap, target_start, donor_start = matcher.longest(doubled[other], doubled[pattern], shared)
                if 2*overlap > size:
                    return dict(kind='relator', target=target, donor=donor,
                        target_rotation=target_start % arena.lengths[other],
                        donor_rotation=donor_start % size, inverse=inverse, overlap=overlap)
    return None


def apply_cyclic_overlap(arena, roots, move):
    """Apply a producer overlap after exact prefix validation; no expansion."""
    target, donor = move['target'], move['donor']
    left, right = roots[target], roots[donor]
    ll, rr = arena.lengths[left], arena.lengths[right]
    i, j, overlap = move['target_rotation'], move['donor_rotation'], move['overlap']
    left = arena.concat(arena.slice(left, i, ll), arena.slice(left, 0, i))
    if move['inverse']:
        right = arena.inverse(right)
    right = arena.concat(arena.slice(right, j, rr), arena.slice(right, 0, j))
    if (not rr//2 < overlap <= min(ll, rr)
            or not arena.equal(arena.slice(left, 0, overlap), arena.slice(right, 0, overlap))):
        raise ArithmeticError('compressed cyclic overlap failed exact prefix replay')
    roots[target] = arena.cyclic_reduce(arena.concat(
        arena.inverse(arena.slice(right, overlap, rr)), arena.slice(left, overlap, ll)))
