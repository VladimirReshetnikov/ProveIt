"""Read-only observers for valid relative Bar--Natan scanning complexes.

The input's chain-homotopy provenance is a mathematical precondition, not
established by this observer. In particular a fabricated scanner is not a knot
certificate. The routine never certifies UNKNOT from a partial scan.
"""
from __future__ import annotations
from .diagram import complete_matching


def dot_degree(value: int) -> int:
    if type(value) is not int or value <= 0:
        raise ValueError("coefficient must be a nonzero bit-packed morphism")
    degree = None
    while value:
        bit = value & -value
        mask = bit.bit_length() - 1
        d = mask.bit_count()
        if degree is None:
            degree = d
        elif d != degree:
            raise ValueError("inhomogeneous coefficient: grade recovery is invalid")
        value ^= bit
    return degree


def overlay_circles(pairs_a, pairs_b) -> int:
    def partner(pairs):
        result = {}
        for a, b in pairs:
            if a == b or a in result or b in result:
                raise ValueError("invalid matching")
            result[a], result[b] = b, a
        return result
    a, b = partner(pairs_a), partner(pairs_b)
    if a.keys() != b.keys():
        raise ValueError("morphisms require a common boundary")
    seen, count = set(), 0
    for start in a:
        if start in seen:
            continue
        count += 1
        d = start
        while d not in seen:
            seen.add(d)
            d = a[d]
            seen.add(d)
            d = b[d]
    return count


def recover_quantum_shifts(matchings, edges):
    """Recover integer potentials on each connected component, up to a constant.

    `edges` contains (source, target, bit-packed coefficient). All objects have
    the same boundary. Cycle consistency is checked; absolute shifts are not
    needed for the residue norm. The function also accepts disconnected input.
    """
    n = len(matchings)
    k = len(matchings[0]) if n else 0
    if any(len(m) != k for m in matchings):
        raise ValueError("unequal boundaries")
    adjacency = [[] for _ in range(n)]
    for a, b, value in edges:
        if not (0 <= a < n and 0 <= b < n):
            raise ValueError("invalid differential endpoint")
        c = overlay_circles(matchings[a], matchings[b])
        if value.bit_length() > (1 << c):
            raise ValueError("coefficient outside the overlay algebra")
        weight = k - c + 2 * dot_degree(value)
        adjacency[a].append((b, weight))
        adjacency[b].append((a, -weight))
    q = [None] * n
    for root in range(n):
        if q[root] is not None:
            continue
        q[root] = 0
        stack = [root]
        while stack:
            a = stack.pop()
            for b, weight in adjacency[a]:
                proposed = q[a] + weight
                if q[b] is None:
                    q[b] = proposed
                    stack.append(b)
                elif q[b] != proposed:
                    raise ValueError("inconsistent quantum potential around a cycle")
    return q


def shift_four(vector, h=0, q=0):
    result = [0] * 4
    sign = -1 if h % 2 else 1
    for j, a in enumerate(vector):
        result[(j + q) % 4] += sign * a
    return tuple(result)


def norm_four(vector):
    return sum(abs(a) for a in vector)


def observe_scan(scan, suffix_pd, *, marked_label):
    """Observe FastScan/ComponentScan's stable state without modifying it.

    The original input must be a validated classical knot; the mark must remain
    in the suffix; all cancellations must be genuine relative equivalences.
    Only physically stored component representatives are visited. Existing
    saturated weights produce a conservative lower bound, not an exact rank.
    No standard-backend files are imported by this module.
    """
    rank_cap = getattr(scan, 'rank_cap', None)
    if rank_cap is not None and (type(rank_cap) is not int or rank_cap < 2):
        raise ValueError('use exact multiplicities or a saturation cap of at least two')
    suffix_pd = tuple(tuple(c) for c in suffix_pd)
    if not suffix_pd or marked_label not in {x for c in suffix_pd for x in c}:
        raise ValueError("the marked arc must remain in a nonempty suffix")
    live = {v for v, m in enumerate(scan.mid) if m is not None}
    adjacent = {v: set() for v in live}
    for v in live:
        for w, value in scan.out[v].items():
            if not value:
                continue
            if w not in live or scan.deg[w] != scan.deg[v] + 1:
                raise ValueError("invalid live differential")
            adjacent[v].add(w)
            adjacent[w].add(v)
    groups, seen = [], set()
    for root in sorted(live):
        if root in seen:
            continue
        seen.add(root)
        group, stack = [], [root]
        while stack:
            v = stack.pop()
            group.append(v)
            for w in adjacent[v]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
        groups.append(sorted(group))
    cache, rows = {}, []
    for group in groups:
        local = {v: i for i, v in enumerate(group)}
        matchings = [scan.algebra.pairs[scan.mid[v]] for v in group]
        edges = [(local[v], local[w], value) for v in group
                 for w, value in scan.out[v].items() if value]
        quantum = recover_quantum_shifts(matchings, edges)
        vector = [0] * 4
        for v, matching, q in zip(group, matchings, quantum):
            key = tuple(tuple(pair) for pair in matching)
            if key not in cache:
                cache[key] = complete_matching(suffix_pd, key).shadow_four()
            shifted = shift_four(cache[key], scan.deg[v], q)
            vector = [a + b for a, b in zip(vector, shifted)]
        multiplicity = 1
        if hasattr(scan, 'owner') and hasattr(scan, 'weights'):
            owner = scan.owner[group[0]]
            if any(scan.owner[v] != owner for v in group):
                raise ValueError("component mixes independent owners")
            weights = scan.weights[owner]
            if any(type(a) is not int or a < 0 for a in weights.values()):
                raise ValueError("multiplicities must be nonnegative integers, not F2")
            multiplicity = sum(weights.values())
        det_norm = abs(vector[0] - vector[2]) + abs(vector[1] - vector[3])
        rows.append(dict(objects=group, relative_q=quantum, shadow=vector,
                         multiplicity=multiplicity, norm=norm_four(vector),
                         euler_abs=abs(sum(vector)), determinant_norm=det_norm))
    total = sum(r['multiplicity'] * r['norm'] for r in rows)
    return dict(reduced_rank_lower_bound=total,
                reduced_rank_lower_bound_capped=min(2,total),
                multiplicities_saturated=rank_cap is not None,
                monotonicity_applies_to=('capped_at_two' if rank_cap is not None else 'full_lower_bound'),
                reduced_euler_lower_bound=sum(r['multiplicity'] * r['euler_abs'] for r in rows),
                reduced_determinant_lower_bound=sum(r['multiplicity'] * r['determinant_norm'] for r in rows),
                unique_completions=len(cache), components=rows,
                precondition='valid marked relative decomposition of the original knot',
                certifies_unknot=False)
