"""Positive rank-two primitive-power evidence on a maintained WordArena.

Adapted from report 45's MIT-0 Christoffel-width argument. This query is
algebraic only. A knot verdict additionally requires a validated diagram and
independent replay of the complete presentation prefix. Noncoherent roots
are skipped, so raw inputs are never silently assumed cyclically reduced.
"""
from math import gcd


def primitive_power_terminal(arena, roots, alive):
    """Return the first supported relator's evidence, or None; never a verdict.

    All current roots retain their slots. The knot-group exponent rows are
    collinear; one shared prefix profile suffices. No grammar is expanded or
    modified, and every pass uses the arena's existing work/cancellation cap.
    """
    arena.tick()
    if len(alive) != 2:
        return None
    labels = sorted(alive)
    if any(type(g) is not int or g <= 0 for g in labels):
        raise ValueError('positive live generator labels required')
    arena.stats['primitive_power_queries'] = arena.stats.get('primitive_power_queries', 0)+1
    positions = {labels[0]:0, -labels[0]:1, labels[1]:2, -labels[1]:3}
    nodes = arena._reachable(roots)
    counts = {0:(0,0,0,0)}
    for node in nodes:
        arena.tick()
        rule = arena.rules[node]
        if rule[0] == 't':
            if rule[1] not in positions:
                raise ValueError('root contains a generator outside the live pair')
            local = [0]*4
            local[positions[rule[1]]] = 1
            counts[node] = tuple(local)
        else:
            counts[node] = tuple(a+b for a,b in zip(counts[rule[1]], counts[rule[2]]))
    ray = None
    for root in roots:
        arena.tick()
        a,A,b,B = counts[root]
        if (a-A) or (b-B):
            d = gcd(abs(a-A),abs(b-B))
            u,v = (a-A)//d,(b-B)//d
            if u < 0 or (u == 0 and v < 0):u,v = -u,-v
            ray = u,v
            break
    if ray is None:
        return None
    u,v = ray
    candidates = []
    for slot,root in enumerate(roots):
        arena.tick()
        a,A,b,B = counts[root]
        if v*(a-A) != u*(b-B):
            return None
        if (a or A or b or B) and not (a and A or b and B):
            candidates.append((slot,root))
    if not candidates:
        return None
    weights = {labels[0]:v, -labels[0]:-v, labels[1]:-u, -labels[1]:u}
    profiles = {0:(0,0,0)}
    for node in nodes:
        arena.tick()
        rule = arena.rules[node]
        if rule[0] == 't':
            h = weights[rule[1]]
            profiles[node] = h,min(0,h),max(0,h)
        else:
            a,lo,hi = profiles[rule[1]]
            b,low,high = profiles[rule[2]]
            profiles[node] = a+b,min(lo,a+low),max(hi,a+high)
    width = abs(u)+abs(v)-1
    for slot,root in candidates:
        arena.tick()
        _,lo,hi = profiles[root]
        if hi-lo == width:
            a,A,b,B = counts[root]
            d = gcd(abs(a-A),abs(b-B))
            arena.stats['primitive_power_hits'] = arena.stats.get('primitive_power_hits',0)+1
            return dict(kind='rank_two_primitive_power', relation=slot, generators=labels,
                        primitive_vector=[(a-A)//d,(b-B)//d], exponent=d,width=width)
    return None
