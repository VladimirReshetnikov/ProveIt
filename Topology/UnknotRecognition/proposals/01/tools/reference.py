"""Independent small-input oracles, deliberately exponential, for validation only.
Dense cube oracle adapted from the supplied baseline's tests/test_fastunknot.py.
Neither oracle uses the optimized scanner's matchings/cobordism operations.
"""
from fastunknot import Diagram


def one_component(strands, word):
    perm = list(range(strands))
    for g in word:
        i = abs(g) - 1
        perm[i], perm[i + 1] = perm[i + 1], perm[i]
    seen = set()
    i = 0
    while i not in seen:
        seen.add(i)
        i = perm[i]
    return len(seen) == strands


def brute_jones(diagram, values=(2, 3), prime=1_000_000_007):
    n = diagram.crossings
    if n == 0:
        return [1 for _ in values]
    totals = [0 for _ in values]
    deltas = [(-a*a-pow(a,-2,prime)) % prime for a in values]
    for state in range(1 << n):
        parent = list(range(2*n))
        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x
        for i,(a,b,c,d) in enumerate(diagram.pd):
            pairs = ((a,d),(b,c)) if state >> i & 1 else ((a,b),(c,d))
            for x,y in pairs:
                parent[find(x)] = find(y)
        circles = len({find(e) for e in range(2*n)})
        exponent = n - 2*state.bit_count()
        for i,a in enumerate(values):
            totals[i] = (totals[i] + pow(a,exponent,prime)*pow(deltas[i],circles,prime)) % prime
    for i,a in enumerate(values):
        totals[i] = totals[i]*pow(deltas[i],-1,prime)*pow(-pow(a,3,prime),-diagram.writhe(),prime) % prime
    return totals


def trefoil_sum(k):
    if k < 1:
        raise ValueError('k must be positive')
    return Diagram.from_braid(k+1, [i for i in range(1,k+1) for _ in range(3)])

def reference_reduced_rank(diagram: Diagram) -> int:
    """Independent dense cube-of-resolutions computation (reduced, F2)."""
    n = diagram.crossings
    if n == 0:
        return 1
    pd = diagram.pd

    def circles(state):
        parent = list(range(2 * n))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for i, (a, b, c, d) in enumerate(pd):
            pairs = ((a, d), (b, c)) if state >> i & 1 else ((a, b), (c, d))
            for x, y in pairs:
                parent[find(x)] = find(y)
        groups = {}
        for e in range(2 * n):
            groups.setdefault(find(e), []).append(e)
        comps = sorted(groups.values())
        owner = {}
        for k, comp in enumerate(comps):
            for e in comp:
                owner[e] = k
        return comps, owner

    data = [circles(s) for s in range(1 << n)]
    # generators: (state, labels tuple with labels[owner[0]] == 1 (x))
    generators = {}
    by_degree = {}
    for s in range(1 << n):
        comps, owner = data[s]
        k = len(comps)
        marked = owner[0]
        for bits in range(1 << k):
            labels = tuple((bits >> j) & 1 for j in range(k))
            if labels[marked] != 1:
                continue
            index = len(generators)
            generators[s, labels] = index
            by_degree.setdefault(bin(s).count("1"), []).append((s, labels))
    columns = {}
    for (s, labels), index in generators.items():
        comps, owner = data[s]
        image = set()
        for i in range(n):
            if s >> i & 1:
                continue
            t = s | (1 << i)
            comps_t, owner_t = data[t]
            out = [None] * len(comps_t)
            src_changed = [j for j, comp in enumerate(comps) if comp not in comps_t]
            tgt_changed = [j for j, comp in enumerate(comps_t) if comp not in comps]
            for j, comp in enumerate(comps):
                if comp in comps_t:
                    out[comps_t.index(comp)] = labels[j]
            if len(src_changed) == 2:
                a, b = (labels[j] for j in src_changed)
                if a and b:
                    continue
                out[tgt_changed[0]] = a | b
                candidates = [tuple(out)]
            else:
                a = labels[src_changed[0]]
                j, k = tgt_changed
                candidates = []
                if a:
                    o = list(out)
                    o[j] = o[k] = 1
                    candidates.append(tuple(o))
                else:
                    for j1, k1 in ((0, 1), (1, 0)):
                        o = list(out)
                        o[j], o[k] = j1, k1
                        candidates.append(tuple(o))
            for cand in candidates:
                key = (t, cand)
                if key in generators:
                    image ^= {generators[key]}
        columns[index] = image
    # rank of d over F2 by elimination on sets
    total_rank = 0
    for h, gens in by_degree.items():
        pivots = {}
        for s, labels in gens:
            col = set(columns[generators[s, labels]])
            while col:
                p = max(col)
                if p in pivots:
                    col ^= pivots[p]
                else:
                    pivots[p] = col
                    break
        total_rank += len(pivots)
    return len(generators) - 2 * total_rank

