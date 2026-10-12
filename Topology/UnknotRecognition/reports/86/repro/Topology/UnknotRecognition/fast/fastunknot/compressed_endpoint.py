"""Exact overlap acceleration from arithmetic endpoint-occurrence sets.

The period and occurrence count are binary integers, with no numerical cap.
Transferred from the 20261008 compressed-certificates research delivery.
The maintained dispatcher first retains its existing two-largest-overlap test.

An endpoint letter or short q-gram proposes an arithmetic progression of all
possible overlap lengths.  Exact SLP equality certifies the required period;
monotone search over candidate ranks then filters the whole progression.
A failed certificate returns None so the complete matcher remains in use.
"""
from .compressed_match import _last


# (count, first start, last start, least gap, greatest gap); empty/singleton
# summaries have zero gaps.  Min/max are exact even when the set is not an AP.
_EMPTY = (0, 0, 0, 0, 0)


def _merge(arena, left, right, shift=0):
    """Concatenate two disjoint, position-ordered occurrence sets."""
    arena.tick()
    nc, first, last, low, high = left
    mc, other_first, other_last, other_low, other_high = right
    if not mc:
        return left
    other_first += shift
    other_last += shift
    if not nc:
        return mc, other_first, other_last, other_low, other_high
    gap = other_first-last
    if gap <= 0:
        raise ArithmeticError('endpoint occurrence sets are not strictly ordered')
    lows = [gap]
    highs = [gap]
    if nc > 1:
        lows.append(low)
        highs.append(high)
    if mc > 1:
        lows.append(other_low)
        highs.append(other_high)
    return nc+mc, first, other_last, min(lows), max(highs)


def occurrence_summary(arena, root, pattern):
    """Summarize every occurrence of an explicit nonempty signed q-gram.

    For g reachable SLP rules and q pattern letters this uses O(q*g) space
    and O(q**2*g + g*log(g)) elementary operations, including topological
    sorting.  Occurrence counts, starts, and gaps use exact binary integers.
    Only the q-1-letter ends of grammar rules are materialized.
    """
    pattern = tuple(pattern)
    if not pattern or any(type(v) is not int or not v for v in pattern):
        raise ValueError('an endpoint pattern must contain nonzero integer letters')
    q = len(pattern)
    arena.tick(q)
    summaries, prefixes, suffixes = {0: _EMPTY}, {0: ()}, {0: ()}
    nodes = arena._reachable([root])
    for node in nodes:
        arena.tick(q)
        rule = arena.rules[node]
        if rule[0] == 't':
            summaries[node] = (1, 0, 0, 0, 0) if q == 1 and rule[1] == pattern[0] else _EMPTY
            if q > 1:
                prefixes[node] = suffixes[node] = (rule[1],)
            continue
        left, right = rule[1:]
        cut = arena.lengths[left]
        summary = summaries[left]
        if q > 1:
            before, after = suffixes[left], prefixes[right]
            # Descending left share gives increasing crossing start positions.
            for share in range(min(q-1, len(before)), max(0, q-len(after)-1), -1):
                arena.tick(q)
                if before[-share:]+after[:q-share] == pattern:
                    position = cut-share
                    summary = _merge(arena, summary, (1, position, position, 0, 0))
            prefixes[node] = (prefixes[left]+prefixes[right])[:q-1]
            suffixes[node] = (suffixes[left]+suffixes[right])[-(q-1):]
        summaries[node] = _merge(arena, summary, summaries[right], cut)
    arena.stats['lcs_anchor_summary_rules'] = arena.stats.get('lcs_anchor_summary_rules', 0)+len(nodes)
    arena.stats['lcs_anchor_summary_calls'] = arena.stats.get('lcs_anchor_summary_calls', 0)+1
    return summaries[root]


def _endpoint(arena, root, size, suffix):
    """Materialize a bounded endpoint, never the expanded source word."""
    end = arena.lengths[root]
    node = arena.slice(root, end-size, end) if suffix else arena.slice(root, 0, size)
    pending, letters = [node], []
    while pending:
        arena.tick()
        current = pending.pop()
        rule = arena.rules[current]
        if rule[0] == 't':
            letters.append(rule[1])
        else:
            pending.extend((rule[2], rule[1]))
    return tuple(letters)


def _small_overlaps(arena, x, y, size):
    result, nx = [], arena.lengths[x]
    for length in range(1, size):
        arena.tick()
        if arena.equal(arena.slice(x, nx-length, nx), arena.slice(y, 0, length)):
            result.append((length, 0, 1))
    return result


def _rank_clip(arena, x, y, ap):
    """Clip a candidate AP whose exact overlap predicate is a true prefix.

    The caller has proved this monotonicity by an endpoint period certificate.
    Maximum/minimum tests handle all/none; backwards doubling brackets the
    last passing candidate, then bisection locates it exactly.  For r candidates
    and b rejected top candidates, there are O(1+log(1+b)) exact comparisons,
    hence O(log(r+1)) in the worst case.  Slice and equality costs are separate.
    """
    arena.tick()
    arena.stats['lcs_anchor_rank_queries'] = arena.stats.get('lcs_anchor_rank_queries', 0)+1
    start, step, count = ap
    length, before = arena.lengths[x], len(arena.rules)

    def matches(index):
        arena.tick()
        arena.stats['lcs_anchor_rank_tests'] = arena.stats.get('lcs_anchor_rank_tests', 0)+1
        candidate = start+index*step
        return arena.equal(arena.slice(x, length-candidate, length),
                           arena.slice(y, 0, candidate))

    try:
        if matches(count-1):
            return ap
        if count == 1 or not matches(0):
            return None
        lo, hi, distance = 0, count-1, 1
        while hi-lo > 1:
            index = max(0, count-1-distance)
            if index <= lo:
                break
            if matches(index):
                lo = index
                break
            hi = index
            distance *= 2
        while hi-lo > 1:
            middle = (lo+hi)//2
            if matches(middle):
                lo = middle
            else:
                hi = middle
        return start, step if lo else 0, lo+1
    finally:
        arena.stats['lcs_anchor_rank_nodes'] = arena.stats.get('lcs_anchor_rank_nodes', 0)+len(arena.rules)-before


def endpoint_overlaps(arena, x, y, *, anchor_sizes=(1, 2, 4, 8)):
    """Return every positive suffix/prefix overlap as disjoint APs, or None.

    None means that no tried endpoint yielded the structural certificate.
    Empty and singleton occurrence sets need no period certificate.  For a
    nonsingleton AP the exact period test is on the longest candidate window,
    not on any trailing/prefix material excluded from every possible overlap.
    A successful q-gram anchor contributes one AP at lengths >= q, plus at
    most q-1 directly checked short lengths.  Both endpoint directions are
    tried.  This function handles unequal lengths by cropping them locally.
    """
    sizes = tuple(anchor_sizes)
    if any(type(q) is not int or q <= 0 for q in sizes):
        raise ValueError('endpoint anchor sizes must be positive integers')
    arena.tick(len(sizes)+1)
    nx, ny = arena.lengths[x], arena.lengths[y]
    limit = min(nx, ny)
    if not limit:
        return []
    if nx > limit:
        x = arena.slice(x, nx-limit, nx)
    if ny > limit:
        y = arena.slice(y, 0, limit)
    summaries, tried = {}, set()
    for proposed in sizes:
        q = min(proposed, limit)
        if q in tried:
            continue
        tried.add(q)
        for from_y in (True, False):
            arena.tick()
            arena.stats['lcs_anchor_trials'] = arena.stats.get('lcs_anchor_trials', 0)+1
            pattern = _endpoint(arena, x if from_y else y, q, from_y)
            root = y if from_y else x
            key = root, pattern
            if key not in summaries:
                summaries[key] = occurrence_summary(arena, root, pattern)
            count, first, last, low, high = summaries[key]
            if count > 1 and low != high:
                continue
            if not count:
                result = _small_overlaps(arena, x, y, q)
            else:
                start = first+q if from_y else limit-last
                ap = start, low if count > 1 else 0, count
                maximum = _last(ap)
                if count == 1:
                    match = arena.equal(arena.slice(x, limit-maximum, limit),
                                        arena.slice(y, 0, maximum))
                    good = ap if match else None
                else:
                    window = (arena.slice(y, 0, maximum) if from_y else
                              arena.slice(x, limit-maximum, limit))
                    if not arena.equal(arena.slice(window, 0, maximum-low),
                                       arena.slice(window, low, maximum)):
                        arena.stats['lcs_anchor_period_rejects'] = arena.stats.get('lcs_anchor_period_rejects', 0)+1
                        continue
                    arena.stats['lcs_anchor_period_checks'] = arena.stats.get('lcs_anchor_period_checks', 0)+1
                    good = _rank_clip(arena, x, y, ap)
                    arena.stats['lcs_anchor_period_bits'] = max(
                        arena.stats.get('lcs_anchor_period_bits', 0), low.bit_length())
                    arena.stats['lcs_anchor_count_bits'] = max(
                        arena.stats.get('lcs_anchor_count_bits', 0), count.bit_length())
                result = _small_overlaps(arena, x, y, q)
                if good is not None:
                    result.append(good)
            arena.stats['lcs_anchor_hits'] = arena.stats.get('lcs_anchor_hits', 0)+1
            arena.stats['lcs_anchor_size_max'] = max(arena.stats.get('lcs_anchor_size_max', 0), q)
            direction = 'suffix' if from_y else 'prefix'
            counter = 'lcs_anchor_'+direction+'_hits'
            arena.stats[counter] = arena.stats.get(counter, 0)+1
            return result
    return None
