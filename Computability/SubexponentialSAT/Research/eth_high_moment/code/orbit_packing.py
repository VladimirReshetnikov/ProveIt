"""Exact finite model of orbit-adaptive collision packing.

This is a packing primitive and validator, not a SAT or contraction solver.
All decisions use integers or Fraction. Repeated edges are permitted.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def labels(r, a):
    return tuple(product(range(r), repeat=a))


def conditional_variance(edges, assignment, q):
    """E[sum_gamma (X_gamma-M/q^2)^2] after a partial labeling."""
    def equal_probability(side, x, y):
        if x == y:
            return Fraction(1)
        ax, ay = assignment.get((side, x)), assignment.get((side, y))
        if ax is not None and ay is not None:
            return Fraction(ax == ay)
        return Fraction(1, q)

    collision_sum = sum(
        equal_probability(0, u, x) * equal_probability(1, v, y)
        for u, v in edges for x, y in edges
    )
    return collision_sum - Fraction(len(edges) ** 2, q ** 2)


def expected_variance_closed(edges, q):
    left, right, multiplicity = Counter(), Counter(), Counter(edges)
    for u, v in edges:
        left[u] += 1
        right[v] += 1
    B = sum(x*x for x in multiplicity.values())
    A = sum(x*x for x in left.values()) + sum(x*x for x in right.values())
    return B * (1-Fraction(1, q))**2 + A * (Fraction(1, q)-Fraction(1, q*q))


def greedy_labels(edges, r, a):
    domain = labels(r, a)
    vertices = sorted({(0, u) for u, _ in edges} | {(1, v) for _, v in edges})
    chosen, trace = {}, []
    q = len(domain)
    initial = conditional_variance(edges, chosen, q)
    for vertex in vertices:
        previous = conditional_variance(edges, chosen, q)
        scores = []
        for label in domain:
            chosen[vertex] = label
            scores.append(conditional_variance(edges, chosen, q))
        require(sum(scores, Fraction()) / q == previous, "Conditional average mismatch")
        best = min(range(q), key=lambda i: (scores[i], i))
        chosen[vertex] = domain[best]
        require(scores[best] <= previous, "Conditional expectation increased")
        trace.append(scores[best])
    require(conditional_variance(edges, chosen, q) <= initial, "Greedy variance failed")
    return chosen, trace


def orbit_pack(edges, assignment, r, a):
    domain = labels(r, a)
    L, q, M = 2**a, r**a, len(edges)
    classes = {(x, y): [] for x in domain for y in domain}
    for e, (u, v) in enumerate(edges):
        classes[assignment[(0, u)], assignment[(1, v)]].append(e)
    orbits = defaultdict(list)
    for x, y in classes:
        orbit = tuple(tuple(sorted((xx, yy))) for xx, yy in zip(x, y))
        orbits[orbit].append((x, y))
    placements, packet_orbits, W = {}, [], 0
    for orbit, members in sorted(orbits.items()):
        k = len(members)
        require(k & (k-1) == 0 and L % k == 0, "Invalid orientation orbit")
        copies = L // k
        maximum = max(len(classes[key]) for key in members)
        H = copies * ((maximum + copies-1) // copies)
        count = H // copies
        start = len(packet_orbits)
        packet_orbits.extend([orbit] * count)
        W += k * H
        for x, y in members:
            slots = [slot for slot in range(L) if all(
                xx == yy or ((slot >> i) & 1) == int(xx > yy)
                for i, (xx, yy) in enumerate(zip(x, y))
            )]
            require(len(slots) == copies, "Incorrect slot multiplicity")
            for j, edge in enumerate(classes[x, y]):
                placements[edge] = (start+j//copies, slots[j % copies])
    require(len(placements) == M, "An edge was lost")
    require(len(set(placements.values())) == M, "A packet slot was reused")
    require(W == L * len(packet_orbits), "Padded size differs from packet size")
    mu = Fraction(M, q*q)
    variance = sum((len(v)-mu)**2 for v in classes.values())
    S2 = sum(len(members)**2 for members in orbits.values())
    R = L * len(orbits)
    require(S2 == (r*(2*r-1))**a, "Orbit second moment identity failed")
    require(R == (r*(r+1))**a, "Orbit rounding identity failed")
    excess = max(0, W-M-R)
    require(excess**2 <= S2*variance, "Adaptive padding bound failed")
    for i in range(a):
        for symbol in range(r):
            for side in (0, 1):
                load = sum(1 for u, v in edges if assignment[(side, (u, v)[side])][i] == symbol)
                require((load-Fraction(M, r))**2 <= Fraction(q*q, r)*variance,
                        "Marginal port bound failed")
    for edge, (packet, slot) in placements.items():
        u, v = edges[edge]
        x, y = assignment[(0, u)], assignment[(1, v)]
        require(tuple(tuple(sorted((xx, yy))) for xx, yy in zip(x, y)) == packet_orbits[packet],
                "Packet orbit identity failed")
        require(all(xx == yy or ((slot >> i) & 1) == int(xx > yy)
                    for i, (xx, yy) in enumerate(zip(x, y))), "Packet orientation failed")
    return dict(packets=len(packet_orbits), padded_slots=W, edges=M,
                variance=variance, S2=S2, R=R, placements=placements)


def scalar(value):
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, dict):
        return {str(k): scalar(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [scalar(v) for v in value]
    return value
