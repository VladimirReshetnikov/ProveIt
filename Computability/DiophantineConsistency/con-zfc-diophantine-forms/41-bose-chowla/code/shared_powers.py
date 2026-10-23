"""A deterministic shared addition chain for the fixed B_4 exponent set.

Every output is a monomial B^e; the exponent of a multiplication is the
sum of its input exponents.  No arithmetic identity beyond this is used.
"""
from collections import Counter


def power_map(d, base, weights):
    W = weights[-1]
    targets = sorted(set(weights) | {W - w for w in weights})
    cache = {0: d.const(1), 1: base}
    parts = {e: {1 << i for i in range(e.bit_length()) if (e >> i) & 1}
             for e in targets}
    for i in range(1, W.bit_length()):
        cache[1 << i] = d.times(cache[1 << (i - 1)], cache[1 << (i - 1)])
    while True:
        counts = Counter()
        for expr in parts.values():
            ordered = sorted(expr)
            counts.update((a, b) for j, a in enumerate(ordered) for b in ordered[j + 1:])
        if not counts:
            break
        pair, count = max(counts.items(),
                          key=lambda item: (item[1], sum(item[0]).bit_count(), -sum(item[0])))
        if count < 2:
            break
        a, b = pair
        if a + b not in cache:
            cache[a + b] = d.times(cache[a], cache[b])
        for expr in parts.values():
            if a in expr and b in expr:
                assert not (a & b)
                expr.remove(a)
                expr.remove(b)
                expr.add(a + b)
    for e, expr in parts.items():
        if e in cache:
            continue
        exponent, node = 0, d.const(1)
        for a in sorted(expr):
            exponent += a
            if exponent in cache:
                node = cache[exponent]
            else:
                node = d.times(node, cache[a])
                cache[exponent] = node
        assert exponent == e
    return {e: cache[e] for e in targets}
