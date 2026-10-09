"""Exact line minimization along powers of one type-II Whitehead automorphism.

Internal producer helpers: roots must already be cyclically freely reduced.
The verifier checks the automorphism independently and does not use this profile.
"""
from collections import Counter


def power_profile(arena, roots, a, subset):
    """Return (first minimizing nonnegative exponent, length delta, unit delta).

    Between consecutive non-a letters x,y, an a-run with signed exponent e
    becomes e+k*d, where d=[x in A]-[-y in A]. Inverse neighbors have d=0,
    so the non-a skeleton cannot cancel. Each changing gap contributes
    |k-t| with t=-e*d. A lower weighted median minimizes their sum.
    DAG multiplicities count gaps without expanding the relators.
    """
    reachable = arena._reachable(roots)
    # first/last non-a letter, signed prefix/suffix a-run lengths
    ends, weights, histogram = {0: (0, 0, 0, 0)}, Counter(), Counter()
    for node in reachable:
        arena.tick()
        rule = arena.rules[node]
        if rule[0] == 't':
            x = rule[1]
            e = 1 if x == a else -1
            ends[node] = (0, 0, e, e) if abs(x) == abs(a) else (x, x, 0, 0)
        else:
            f, l, p, s = ends[rule[1]]
            g, h, q, t = ends[rule[2]]
            ends[node] = (f or g, h or l, p if f else p+q, t if h else s+t)

    def gap(x, y, exponent, weight):
        arena.tick()
        slope = int(x in subset)-int(-y in subset)
        if slope:
            histogram[-exponent*slope] += weight

    for root in roots:
        arena.tick()
        weights[root] += 1
        first, last, prefix, suffix = ends[root]
        if first:
            gap(last, first, suffix+prefix, 1)
    for node in reversed(reachable):
        arena.tick()
        rule, weight = arena.rules[node], weights[node]
        if rule[0] == 'c':
            left, right = rule[1:]
            weights[left] += weight
            weights[right] += weight
            if ends[left][1] and ends[right][0]:
                gap(ends[left][1], ends[right][0], ends[left][3]+ends[right][2], weight)
    if not histogram:
        return 0, 0, 0
    # Charge sorting as well as scans; integer bit costs are discussed separately.
    arena.tick(len(histogram)*(len(histogram).bit_length()+3))
    total, cumulative, exponent = sum(histogram.values()), 0, 0
    for point in sorted(histogram):
        cumulative += histogram[point]
        if 2*cumulative >= total:
            exponent = max(0, point)
            break
    delta = sum(weight*(abs(exponent-point)-abs(point)) for point, weight in histogram.items())
    unit = sum(weight*(1 if point <= 0 else -1) for point, weight in histogram.items())
    return exponent, delta, unit


def powered_images(arena, alive, a, subset, exponent):
    """Producer substitution for a positive power; inverse letters stay exact."""
    positive = arena.power(arena.letter(a), exponent)
    negative = arena.inverse(positive)
    images = {}
    for g in alive:
        image = arena.letter(g)
        if g != abs(a):
            if -g in subset:
                image = arena.concat(negative, image)
            if g in subset:
                image = arena.concat(image, positive)
        images[g] = image
        images[-g] = arena.inverse(image)
    return images
