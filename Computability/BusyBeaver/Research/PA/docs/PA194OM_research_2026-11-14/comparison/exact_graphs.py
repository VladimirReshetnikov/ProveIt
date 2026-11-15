#!/usr/bin/env python3
"""Exact isomorphism for finite deterministic binary TM action graphs.

Read symbols and write/move actions are preserved; all missing-target labels
mean termination. Start controls are deliberately not part of this relation.
Color refinement prunes impossible matches; only a verified full bijection
can certify equality, so disconnected components cause no hash shortcut.
"""
from collections import Counter, defaultdict


def isomorphism(left, right):
    """Return a complete working-state bijection, or None.

    Inputs are dictionaries (control,read_bit)->(write_bit,direction,next).
    """
    aa = {q for q, b in left}
    bb = {q for q, b in right}
    if len(aa) != len(bb):
        return None
    ga, gb = left, right
    sets = (aa, bb)
    graphs = (ga, gb)
    nodes = [(i, q) for i in (0, 1) for q in sorted(sets[i])]
    incoming = {v: [] for v in nodes}
    initial = {}
    for i, q in nodes:
        g, s = graphs[i], sets[i]
        initial[i, q] = tuple((g[q, bit][0], g[q, bit][1], g[q, bit][2] in s) for bit in (0, 1))
        for bit in (0, 1):
            nxt = g[q, bit][2]
            if nxt in s:
                incoming[i, nxt].append((bit, (i, q)))
    palette = {sig: k for k, sig in enumerate(sorted(set(initial.values())))}
    color = {v: palette[initial[v]] for v in nodes}
    while True:
        if Counter(color[0, q] for q in aa) != Counter(color[1, q] for q in bb):
            return None
        signatures = {}
        for i, q in nodes:
            g, s = graphs[i], sets[i]
            signatures[i, q] = (color[i, q],
                tuple(color[i, g[q, bit][2]] if g[q, bit][2] in s else -1 for bit in (0, 1)),
                tuple(sorted((bit, color[p]) for bit, p in incoming[i, q])))
        palette = {sig: k for k, sig in enumerate(sorted(set(signatures.values())))}
        new_color = {v: palette[signatures[v]] for v in nodes}
        stable = len(set(new_color.values())) == len(set(color.values()))
        color = new_color
        if stable:
            break
    if Counter(color[0, q] for q in aa) != Counter(color[1, q] for q in bb):
        return None
    candidates = defaultdict(list)
    for q in sorted(bb):
        candidates[color[1, q]].append(q)

    def propagate(p, q, mapping, inverse):
        mapping, inverse = mapping.copy(), inverse.copy()
        todo = [(p, q)]
        while todo:
            p, q = todo.pop()
            if p in mapping:
                if mapping[p] != q:
                    return None
                continue
            if q in inverse or color[0, p] != color[1, q]:
                return None
            mapping[p], inverse[q] = q, p
            for bit in (0, 1):
                w, d, nxt = ga[p, bit]
                v, e, target = gb[q, bit]
                if (w, d, nxt in aa) != (v, e, target in bb):
                    return None
                if nxt in aa:
                    todo.append((nxt, target))
        return mapping, inverse

    def search(mapping, inverse):
        if len(mapping) == len(aa):
            return mapping
        p = min((p for p in aa if p not in mapping),
                key=lambda p: (sum(q not in inverse for q in candidates[color[0, p]]), -len(incoming[0, p]), p))
        for q in candidates[color[0, p]]:
            if q in inverse:
                continue
            extension = propagate(p, q, mapping, inverse)
            if extension is not None:
                result = search(*extension)
                if result is not None:
                    return result
        return None
    return search({}, {})


def partition_nonspanning(class_list, cache, table_directory):
    """Refine partial-component hash buckets using exact whole-graph tests."""
    from inventory_tables import parse
    result = []
    for c in class_list:
        if c["exact"]:
            c["class_id"] = str(c["states"]) + ":" + c["unrooted_hash"]
            c["identity_basis"] = "complete rooted traversal over every state"
            result.append(c)
            continue
        groups = []
        for digest in sorted(c["content_hashes"]):
            rows, states, start = parse((table_directory / (digest + ".tm")).read_bytes())
            for group in groups:
                if isomorphism(rows, group["rows"]) is not None:
                    group["hashes"].append(digest)
                    break
            else:
                groups.append({"rows": rows, "hashes": [digest]})
        for group in groups:
            hashes = group["hashes"]
            item = dict(c)
            item["content_hashes"] = hashes
            item["rooted_hashes"] = sorted({cache[h]["rooted_hash"] for h in hashes if cache[h]["rooted_hash"] is not None})
            # Memberships are assigned by the finalizer from occurrence hashes.
            item["class_id"] = str(c["states"]) + ":nonspanning:" + min(hashes)
            item["identity_basis"] = "exact complete-bijection search after color refinement"
            item["complete_identity_check"] = True
            result.append(item)
    return result
