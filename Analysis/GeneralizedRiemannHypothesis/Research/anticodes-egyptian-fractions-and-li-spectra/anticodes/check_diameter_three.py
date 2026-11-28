"""Certificate checker for diameter three in every A_n. Python 3 standard library."""

from fractions import Fraction
from itertools import combinations_with_replacement, product
from math import comb, lcm

CALIBRATION = 15
PARTITIONS = ((3,), (2, 1), (1, 1, 1))


def target(N):
    return N + N * comb(N, 2)


def difference(N, j):
    return sum((-1) ** (j - t) * comb(j, t) * target(N + t)
               for t in range(j + 1))


def anchor_lens(h):
    """Enumerate all sum-zero points within l1 distance six of both anchors."""
    def visit(i, pos0, neg0, posh, negh, prefix):
        if i == len(h):
            if pos0 == neg0 and any(prefix) and prefix != h:
                yield prefix
            return
        low = max(-neg0, h[i] - negh)
        high = min(pos0, h[i] + posh)
        for a in range(low, high + 1):
            delta = a - h[i]
            yield from visit(i + 1, pos0 - max(a, 0), neg0 - max(-a, 0),
                             posh - max(delta, 0), negh - max(-delta, 0),
                             prefix + (a,))
    return list(visit(0, 3, 3, 3, 3, ()))


def tokens(point):
    return tuple(6 * axis + (0 if a > 0 else 3) + level
                 for axis, a in enumerate(point) for level in range(abs(a)))


def graph_rows(sets, N):
    """Bitset intersection counts implement the exact l1 distance test."""
    size = len(sets)
    width = (size + 7) // 8
    occurrence = [bytearray(width) for _ in range(6 * N)]
    mass_class = [bytearray(width) for _ in range(4)]
    for i, member in enumerate(sets):
        byte, bit = i // 8, 1 << (i % 8)
        mass_class[len(member) // 2][byte] |= bit
        for token in member:
            occurrence[token][byte] |= bit
    columns = [int.from_bytes(a, 'little') for a in occurrence]
    masses = [int.from_bytes(a, 'little') for a in mass_class]
    all_bits = (1 << size) - 1
    for i, member in enumerate(sets):
        one = two = three = 0
        for token in member:
            column = columns[token]
            three |= two & column
            two |= one & column
            one |= column
        at_least = (all_bits, one, two, three)
        row = 0
        for half_mass, pool in enumerate(masses):
            required = max(0, len(member) // 2 + half_mass - 3)
            row |= at_least[required] & pool
        yield row & ~(1 << i)


def balanced_centers(h):
    support = sum(a != 0 for a in h)
    intervals = [range(min(0, a), max(0, a) + 1) for a in h[:support]]
    return [v + (0,) * (len(h) - support) for v in product(*intervals)
            if sum(map(abs, v)) == 3 and abs(sum(v)) == 1]


def bitset(indices, size):
    raw = bytearray((size + 7) // 8)
    for i in indices:
        raw[i // 8] |= 1 << (i % 8)
    return int.from_bytes(raw, 'little')


def weights_and_bound(N, s, j):
    if j == 0:
        return [1] * 4, target(N) - 2
    weights = [Fraction(comb(N - s, k - j), comb(N - s, k)) if k >= j
               else Fraction(0) for k in range(4)]
    scale = lcm(*(item.denominator for item in weights))
    return [int(scale * item) for item in weights], scale * difference(N, j)


def verify(verts, h, j, equality=False):
    """Disprove existence of an overweight clique or a noncanonical equality."""
    N, s = len(h), sum(a != 0 for a in h)
    free_weight, bound = weights_and_bound(N, s, j)
    points, weights = [], []
    for point in verts:
        k = sum(a != 0 for a in point[s:])
        assert k <= 3
        if free_weight[k]:
            points.append(point)
            weights.append(free_weight[k])
    sets = list(map(tokens, points))
    degrees = [a.bit_count() for a in graph_rows(sets, N)]
    perm = sorted(range(len(sets)), key=lambda i: (degrees[i], weights[i]), reverse=True)
    adj = list(graph_rows([sets[i] for i in perm], N))
    points = [points[i] for i in perm]
    weights = [weights[i] for i in perm]
    size = len(weights)
    all_points = (1 << size) - 1
    covers = []
    if equality:
        assert j == 0
        for center in balanced_centers(h):
            covers.append(bitset((i for i, point in enumerate(points)
                                  if sum(abs(a - b) for a, b in zip(point, center)) <= 3),
                                 size))
    vertices_in = [sum(((cover >> i) & 1) << c for c, cover in enumerate(covers))
                   for i in range(size)]
    nodes = 0

    def violates(pool, need, eligible):
        nonlocal nodes
        nodes += 1
        if need <= 0:
            return not equality or eligible == 0
        if not pool:
            return False
        if equality:
            mask = eligible
            while mask:
                low = mask & -mask
                if pool & ~covers[low.bit_length() - 1] == 0:
                    return False
                mask ^= low

        # Cover vertices by independent sets of integer multiplicity,
        # paying at most need-1. Each clique uses at most one per set.
        residual = weights.copy()
        uncovered = pool
        budget = need - 1
        while uncovered and budget:
            chosen = []
            candidates = uncovered
            cost = budget
            while candidates:
                low = candidates & -candidates
                i = low.bit_length() - 1
                chosen.append(i)
                cost = min(cost, residual[i])
                candidates &= ~(low | adj[i])
            for i in chosen:
                residual[i] -= cost
                if residual[i] == 0:
                    uncovered ^= 1 << i
            budget -= cost

        # A clique with sufficient weight contains an uncovered vertex.
        # Group candidates by their first such vertex.
        while uncovered:
            low = uncovered & -uncovered
            i = low.bit_length() - 1
            pool ^= low
            uncovered ^= low
            if violates(pool & adj[i], need - weights[i], eligible & vertices_in[i]):
                return True
        return False

    sought = bound if equality else bound + 1
    bad = violates(all_points, sought, (1 << len(covers)) - 1)
    assert not bad, (N, h, j, equality)
    return nodes


def main():
    print("N  partitions(+/-)   size   equality   lift-j=1,2,3  (search nodes)", flush=True)
    for N in range(2, CALIBRATION + 1):
        for pos, neg in combinations_with_replacement(PARTITIONS, 2):
            s = len(pos) + len(neg)
            if s > N:
                continue
            h = pos + tuple(-a for a in neg) + (0,) * (N - s)
            verts = anchor_lens(h)
            size = verify(verts, h, 0)
            eq = verify(verts, h, 0, equality=True)
            lift = [verify(verts, h, j) for j in range(1, 4)] if N == CALIBRATION else []
            print(N, ''.join(map(str, pos)) + '/' + ''.join(map(str, neg)),
                  size, eq, *lift, flush=True)
    print("All finite size, equality, and lifting inequalities verified.")


if __name__ == '__main__':
    main()
