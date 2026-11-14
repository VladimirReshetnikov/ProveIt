"""Fast discovery for one/two added read-only contextual routers.

Each router h has rows (0,R,u),(1,R,w), with old-state children u,w.
The router is absent from the raw source machine and occurs only in the
explicitly checked replacement detours. All old raw incoming premises hold.
"""
from pathlib import Path
import collections, itertools, sys, os
P = Path(os.environ['PA195_REFERENCE'])
sys.path.insert(0, str(P))
import build_verify as v
c = v.c


def matching(edges):
    byleft = collections.defaultdict(list)
    for a, b in edges:
        byleft[a].append(b)
    match = {}
    def aug(a, seen):
        for b in byleft[a]:
            if b in seen:
                continue
            seen.add(b)
            if b not in match or aug(match[b], seen):
                match[b] = a
                return True
        return False
    for a in byleft:
        aug(a, set())
    return len(match)


def signatures(raw, shape):
    """Return base valid edges, per-edge missing-bit masks, router bit masks.

    A router that cannot supply any currently missing branch cannot improve
    the optimistic matching number; omitting it is safe for that filter.
    """
    states = {q for q, b in raw}
    incoming = collections.defaultdict(set)
    byact = [collections.defaultdict(list), collections.defaultdict(list)]
    providers = [collections.defaultdict(list), collections.defaultdict(list)]
    for (q, bit), (w, d, n) in raw.items():
        incoming[n].add((w, d))
        byact[bit][raw[q, bit]].append(q)
    for h in states:
        w0, d0, u0 = raw[h, 0]
        w1, d1, u1 = raw[h, 1]
        if (w0, d0, w1, d1) != (0, True, 1, True):
            continue
        for bit in (0, 1):
            if (u0, bit) in raw and (u1, bit) in raw:
                providers[bit][(raw[u0, bit], raw[u1, bit])].append((h, u0, u1))
    left = [q for q in shape if incoming[q] == {(0, True)}]
    right = [q for q in shape if incoming[q] == {(1, True)}]
    base, missing = set(), {}
    flags = collections.defaultdict(lambda: collections.defaultdict(int))
    for a, b in itertools.product(left, right):
        need = 0
        for bit in (0, 1):
            if raw[a, bit] == raw[b, bit]:
                continue
            key = raw[a, bit], raw[b, bit]
            if not any(not {a, b} & {h, u0, u1}
                       for h, u0, u1 in providers[bit].get(key, ())):
                need |= 1 << bit
        if not need:
            base.add((a, b))
            continue
        missing[a, b] = need
        for bit in (0, 1):
            if not (need & (1 << bit)):
                continue
            for u0, u1 in itertools.product(byact[bit][raw[a, bit]],
                                           byact[bit][raw[b, bit]]):
                if not {a, b} & {u0, u1}:
                    flags[u0, u1][a, b] |= 1 << bit
    return base, missing, dict(flags)


def one_router_candidates(raw, shape, desired_states=194):
    base, missing, flags = signatures(raw, shape)
    target = len(raw) // 2 + 1 - desired_states
    best = len(raw) // 2 + 1 - matching(base)
    hits = []
    distinct = {}
    for router, enabled in flags.items():
        extra = frozenset(edge for edge, bits in enabled.items()
                          if bits & missing[edge] == missing[edge])
        # Duplicate edge sets have identical optimistic score, but retain all
        # routers for exact local compatibility, whose traces may differ.
        if extra not in distinct:
            distinct[extra] = matching(base | extra)
        upper = distinct[extra]
        best = min(best, len(raw) // 2 + 1 - upper)
        if upper >= target:
            hits.append((router, upper))
    return {'best_optimistic': best, 'router_signatures': len(flags),
            'distinct_extra_edge_sets': len(distinct), 'target_folds': target,
            'hits': hits}


def two_router_candidates(raw, shape, desired_states=194):
    base, missing, flags = signatures(raw, shape)
    target = len(raw) // 2 + 2 - desired_states
    initial = matching(base)
    best = len(raw) // 2 + 2 - initial
    groups = collections.defaultdict(list)
    for router, enabled in flags.items():
        groups[tuple(sorted(enabled.items()))].append(router)
    grouped = [(dict(mask), routers) for mask, routers in groups.items()]
    hits, cached = [], {}
    for i, (ma, ra) in enumerate(grouped):
        for mb, rb in grouped[i + 1:]:
            enabled = ma.copy()
            for edge, bits in mb.items():
                enabled[edge] = enabled.get(edge, 0) | bits
            extra = frozenset(edge for edge, bits in enabled.items()
                              if bits & missing[edge] == missing[edge])
            if extra not in cached:
                cached[extra] = matching(base | extra)
            upper = cached[extra]
            best = min(best, len(raw) // 2 + 2 - upper)
            if upper >= target:
                # Retain distinct helper implementations in each signature
                # class; exact trace compatibility may depend on their rows.
                hits.append((ra, rb, upper))
    return {'best_optimistic': best, 'router_signatures': len(flags),
            'signature_groups': len(grouped), 'target_folds': target,
            'distinct_extra_edge_sets': len(cached), 'hits': hits}


def exact_folds(raw, shape, routers, target):
    """Return (folded,folds,certificate,raw_with_helpers), or None.

    The certificate simulates raw, not raw_with_helpers: helper controls do
    not occur in the simulated machine and all uses lie inside checked
    two-cell detours. This permits broader incoming-history bookkeeping.
    """
    states = {q for q, b in raw}
    labels, q = [], 1998
    for _ in routers:
        while q in states:
            q -= 1
        labels.append(q); states.add(q); q -= 1
    rr = raw.copy()
    for h, (u0, u1) in zip(labels, routers):
        rr[h, 0] = (0, True, u0)
        rr[h, 1] = (1, True, u1)
    ops = c.opportunities_fast(rr, shape, ignore_incoming=set(labels))
    if len(c.max_matching(ops)) < target:
        return None
    fs, used, answer = [], set(), None
    def search(i):
        nonlocal answer
        if len(fs) == target:
            try:
                folded, aliases = v.quotient(rr, fs)
                cert = v.quotient_certificate(raw, folded, fs, aliases)
                answer = (folded, list(fs), cert, rr)
                return True
            except (ValueError, KeyError):
                return False
        if len(fs) + len(ops) - i < target:
            return False
        a, b, choices = ops[i]
        if a not in used and b not in used:
            used.update((a, b))
            for acts in itertools.product(*choices):
                fs.append((a, b, acts))
                if search(i + 1):
                    return True
                fs.pop()
            used.difference_update((a, b))
        return search(i + 1) if i + 1 < len(ops) else False
    search(0)
    return answer


if __name__ == '__main__':
    import json, time
    for path, scanner in [(P / 'grammar.json', False),
                          (Path(__file__).parent / 'pa195_scanner8/grammar.json', True)]:
        t = c.read_grammar(path)
        raw, ix, shape = c.build(t)
        if scanner:
            raw[34, 0] = (0, False, 1999)
            raw[1999, 0] = (0, False, 75)
            raw[1999, 1] = (1, False, 2)
        tick = time.time()
        result = one_router_candidates(raw, shape)
        print(scanner, json.dumps(result), time.time() - tick)
