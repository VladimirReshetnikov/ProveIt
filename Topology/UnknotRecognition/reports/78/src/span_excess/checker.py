"""Independent arithmetic replay: this module imports no producer or solver.

The certificates prove finite optimization statements, never knot verdicts.
"""
from __future__ import annotations


def _ints(xs):
    return all(type(x) is int for x in xs)


def check_feasible(n, arcs, potential) -> bool:
    return (type(n) is int and n > 0 and len(potential) == n and _ints(potential)
            and all(len(a) == 3 and _ints(a) and 0 <= a[0] < n
                    and 0 <= a[1] < n and potential[a[1]]-potential[a[0]] <= a[2]
                    for a in arcs))


def check_negative_cycle(n, arcs, certificate) -> bool:
    try:
        if type(n) is not int or n <= 0 or any(len(a) != 3 or not _ints(a)
                or not (0 <= a[0] < n and 0 <= a[1] < n) for a in arcs):
            return False
        ids = certificate['cycle']
        if certificate['status'] != 'INFEASIBLE' or not ids or not _ints(ids):
            return False
        if any(i < 0 or i >= len(arcs) for i in ids):
            return False
        rows = [arcs[i] for i in ids]
        if any(not _ints(row) or not (0 <= row[0] < n and 0 <= row[1] < n)
               for row in rows):
            return False
        return (all(rows[i][1] == rows[(i+1) % len(rows)][0] for i in range(len(rows)))
                and sum(row[2] for row in rows) < 0)
    except (KeyError, TypeError, IndexError, ValueError):
        return False


def check_optimum(n, edges, arcs, certificate) -> bool:
    try:
        if certificate['status'] != 'OPTIMAL':
            return False
        p = certificate['potential']
        f, lam = certificate['edge_flows'], certificate['constraint_flows']
        if not check_feasible(n, arcs, p):
            return False
        if len(f) != len(edges) or len(lam) != len(arcs):
            return False
        if not _ints(f) or not _ints(lam) or any(x < 0 for x in lam):
            return False
        balance = [0]*n
        primal = dual = 0
        for row, flow in zip(edges, f):
            if len(row) != 4 or not _ints(row):
                return False
            u, v, c, w = row
            if not (0 <= u < n and 0 <= v < n and w >= 0 and -w <= flow <= w):
                return False
            primal += w*abs(c+p[v]-p[u])
            dual += flow*c
            balance[u] -= flow
            balance[v] += flow
        for (u, v, b), flow in zip(arcs, lam):
            dual -= flow*b
            balance[u] -= flow
            balance[v] += flow
        return (not any(balance) and type(certificate['objective']) is int
                and primal == dual == certificate['objective'])
    except (KeyError, TypeError, IndexError, ValueError):
        return False


def check_model(model) -> bool:
    """Independent balanced-anchor check; no call to HeightModel.validate."""
    try:
        n = model.n
        if type(n) is not int or n <= 0 or not model.vertices:
            return False
        t = len(model.vertices)
        if not (t == len(model.heights) == len(model.low) == len(model.high)):
            return False
        if len(model.initial) != n or not _ints(model.initial):
            return False
        balance = [0]*n
        seen = set()
        primal = dual = 0
        for vs, hs, lo, hi in zip(model.vertices, model.heights, model.low, model.high):
            if len(vs) != 4 or len(hs) != 4 or not _ints(vs) or not _ints(hs):
                return False
            if not (type(lo) is int and type(hi) is int and 0 <= lo < 4 and 0 <= hi < 4):
                return False
            if any(v < 0 or v >= n for v in vs):
                return False
            seen.update(vs)
            a = [h+model.initial[v] for v, h in zip(vs, hs)]
            primal += max(a)-min(a)
            dual += hs[hi]-hs[lo]
            balance[vs[hi]] += 1
            balance[vs[lo]] -= 1
        for row in model.edges:
            if len(row) != 4 or not _ints(row):
                return False
            if not (0 <= row[0] < n and 0 <= row[1] < n and row[3] >= 0):
                return False
        return (seen == set(range(n)) and not any(balance)
                and type(model.optimum) is int and primal == dual == model.optimum)
    except (AttributeError, TypeError, IndexError):
        return False


def replay_cell(model, entry, extra=()) -> bool:
    """Reconstruct all inequalities independently from sparse cell data."""
    try:
        if not check_model(model):
            return False
        slots = [None]*(2*len(model.vertices))
        previous = -1
        excess = 0
        for s, d, j in entry['stratum']:
            if not _ints((s, d, j)) or not (previous < s < len(slots) and d > 0 and 0 <= j < 4):
                return False
            anchor = model.high[s//2] if s % 2 == 0 else model.low[s//2]
            if j == anchor:
                return False
            slots[s] = (d, j)
            previous, excess = s, excess+d
        if type(entry['excess']) is not int or entry['excess'] != excess:
            return False
        arcs = list(extra)
        for t, (vs, hs) in enumerate(zip(model.vertices, model.heights)):
            lo, hi = model.low[t], model.high[t]
            up, j = slots[2*t] or (0, hi)
            down, l = slots[2*t+1] or (0, lo)
            # Must match producer order for indexed duals: extras come LAST.
            for i in range(4):
                arcs.append((vs[hi], vs[i], hs[hi]-hs[i]+up))
                arcs.append((vs[i], vs[lo], hs[i]-hs[lo]+down))
            if up:
                arcs.append((vs[j], vs[hi], hs[j]-hs[hi]-up))
            if down:
                arcs.append((vs[lo], vs[l], hs[lo]-hs[l]-down))
        if extra:
            arcs = arcs[len(extra):] + list(extra)
        proof = entry['proof']
        if proof['status'] == 'INFEASIBLE':
            return check_negative_cycle(model.n, arcs, proof)
        if not check_optimum(model.n, model.edges, arcs, proof):
            return False
        p = proof['potential']
        span = sum(max(h+p[v] for v, h in zip(vs, hs))-
                   min(h+p[v] for v, h in zip(vs, hs))
                   for vs, hs in zip(model.vertices, model.heights))
        return (span == model.optimum+excess and entry['excess'] == excess
                and entry['score2'] == 2*span-proof['objective'])
    except (KeyError, TypeError, IndexError, ValueError):
        return False


def replay_band(model, answer) -> bool:
    """Check exhaustive coverage by cardinality plus distinct valid descriptions.

    A complete log is necessary. An optimum from one stratum or a truncated log
    is deliberately rejected. Memory is proportional to the supplied log.
    """
    from math import comb
    try:
        if not check_model(model) or answer['schema'] != 'span-excess-band-v1':
            return False
        if answer['status'] != 'COMPLETE':
            return False
        k, rows = answer['radius'], answer['cells']
        if type(k) is not int or k < 0 or not isinstance(rows, list):
            return False
        slots = 2*len(model.vertices)
        expected = sum(comb(slots, j)*3**j*comb(k, j)
                       for j in range(min(slots, k)+1))
        if len(rows) != expected:
            return False
        seen, maxima, best_pair, best_exists = set(), {}, None, False
        for row in rows:
            key = tuple(tuple(a) for a in row['stratum'])
            if key in seen or sum(d for _, d, _ in key) > k:
                return False
            if not replay_cell(model, row, answer['extra_constraints']):
                return False
            seen.add(key)
            if row['proof']['status'] == 'OPTIMAL':
                q, score = row['excess'], row['score2']
                maxima[str(q)] = max(maxima.get(str(q), score), score)
                pair = (score, -q)
                if best_pair is None or pair > best_pair:
                    best_pair = pair
                if row == answer['best']:
                    best_exists = True
        if best_pair is None:
            return answer['best'] is None and not answer['profile']
        best = answer['best']
        if not best_exists or (best['score2'], -best['excess']) != best_pair:
            return False
        if set(answer['profile']) != set(maxima):
            return False
        return all(answer['profile'][q] in rows
                   and answer['profile'][q]['excess'] == int(q)
                   and answer['profile'][q]['score2'] == value
                   for q, value in maxima.items())
    except (KeyError, TypeError, IndexError, ValueError, AttributeError):
        return False


def check_lexicographic(model, answer) -> bool:
    try:
        if not check_model(model) or answer['schema'] != 'edge-then-span-v1':
            return False
        first, second = answer['first'], answer['second']
        if not check_optimum(model.n, model.edges, (), first):
            return False
        constraints = []
        for (u, v, c, w), f in zip(model.edges, first['edge_flows']):
            if w > 0:
                if f != w:
                    constraints.append((u, v, -c))
                if f != -w:
                    constraints.append((v, u, c))
        objective = []
        for t, (vs, hs) in enumerate(zip(model.vertices, model.heights)):
            upper, lower = model.n+2*t, model.n+2*t+1
            objective.append((lower, upper, 0, 1))
            for v, h in zip(vs, hs):
                constraints.append((upper, v, -h))
                constraints.append((v, lower, h))
        if not check_optimum(model.n+2*len(model.vertices), objective, constraints, second):
            return False
        p = second['potential'][:model.n]
        span = sum(max(h+p[v] for v, h in zip(vs, hs))-
                   min(h+p[v] for v, h in zip(vs, hs))
                   for vs, hs in zip(model.vertices, model.heights))
        F = sum(w*abs(c+p[v]-p[u]) for u,v,c,w in model.edges)
        return (p == answer['potential'] and F == first['objective'] == answer['edge_objective']
                and span == second['objective'] == answer['span']
                and answer['score2'] == 2*span-F)
    except (KeyError, TypeError, IndexError, ValueError, AttributeError):
        return False
