"""Independent, deliberately exponential finite oracles. Never production code."""
from itertools import combinations, product
from functools import lru_cache


def peel_subset(counts, subset, allowed=None):
    live = set(subset)
    if allowed is None:
        allowed = {(r, c) for r in counts for c, a in counts[r].items() if a == 1}
    while live:
        choice = None
        columns = {c for r in live for c, a in counts[r].items() if a}
        for c in columns:
            users = [r for r in live if counts[r].get(c, 0)]
            if len(users) == 1 and (users[0], c) in allowed:
                choice = users[0]; break
        if choice is None: return False
        live.remove(choice)
    return True


def brute_private(counts, weights=None, allowed=None):
    rows = sorted(counts)
    if weights is None: weights = dict.fromkeys(rows, 1)
    best = 0
    for mask in range(1 << len(rows)):
        subset = [r for i, r in enumerate(rows) if mask >> i & 1]
        score = sum(weights[r] for r in subset)
        if score > best and peel_subset(counts, subset, allowed): best = score
    return best


def arbitrary_positive_optimum(counts, weights=None):
    rows = sorted(counts)
    cols = sorted({c for r in rows for c, a in counts[r].items() if a})
    if weights is None: weights = dict.fromkeys(rows, 1)
    initial = tuple((r, tuple(min(2, counts[r].get(c, 0)) for c in cols)) for r in rows)
    @lru_cache(None)
    def solve(state):
        best = 0
        for i, (r, donor) in enumerate(state):
            for c, a in enumerate(donor):
                if a != 1: continue
                remainder = []
                for j, (s, row) in enumerate(state):
                    if i == j: continue
                    out = tuple(0 if h == c else min(2, row[h] + row[c] * donor[h])
                                for h in range(len(cols)))
                    remainder.append((s, out))
                best = max(best, weights[r] + solve(tuple(remainder)))
        return best
    return solve(initial)


def literal_transport(counts, pairs):
    rows = {r: {c: a for c, a in row.items() if a} for r, row in counts.items()}
    for r, c in pairs:
        donor = rows.pop(r)
        assert donor.pop(c) == 1
        for row in rows.values():
            amount = row.pop(c, 0)
            if amount:
                for h, a in donor.items(): row[h] = row.get(h, 0) + amount * a
    return rows


def path_oracle(length, weight=1, first_is_row=True, eligibility=(True, True),
                potentials=((0, 0), (0, 0))):
    result = {}
    for bits in product((0, 1), repeat=length):
        if any(bits[i] + bits[i + 1] > 1 for i in range(length - 1)): continue
        if any(bits[i] and not eligibility[i % 2] for i in range(length)): continue
        orientations = []
        value = sum(bits) * weight
        for i, chosen in enumerate(bits):
            isrow = first_is_row if i % 2 == 0 else not first_is_row
            orientations.append(1 if (chosen == 1) == isrow else -1)
            if i:
                occupied = bool(bits[i - 1] or bits[i])
                value += potentials[0 if isrow else 1][0 if occupied else 1]
        d = orientations[0] if len(set(orientations)) == 1 else 0
        key = bits[0], bits[-1], d
        result[key] = max(result.get(key, -1), value)
    return result


def cycle_counts(n):
    if n < 2: raise ValueError
    return {i: {i: 1, (i + 1) % n: 1} for i in range(n)}


def cactus_counts(n, *, weights=False):
    # n four-cycles sharing one column; every other vertex is fresh.
    counts, w = {}, {}
    for i in range(n):
        counts[2*i] = {0: 1, i+1: 1}
        counts[2*i+1] = {0: 1, i+1: 1}
        w[2*i], w[2*i+1] = i+1, 2*i+3
    return (counts, w) if weights else counts


def spanning_forests(n, edges):
    def roots(chosen):
        p = list(range(n))
        def find(v):
            while p[v] != v: v = p[v]
            return v
        for e in chosen:
            a, b = map(find, edges[e])
            if a == b: return None
            p[a] = b
        return tuple(find(v) for v in range(n))
    labels = sorted(edges)
    # Compute source component count, allowing all cycles.
    p = list(range(n))
    def find(v):
        while p[v] != v: v = p[v]
        return v
    for a, b in edges.values(): p[find(a)] = find(b)
    size = n - len({find(v) for v in range(n)})
    for comb in combinations(labels, size):
        r = roots(comb)
        if r is None: continue
        if all(r[a] == r[b] for a, b in edges.values()): yield set(comb)
