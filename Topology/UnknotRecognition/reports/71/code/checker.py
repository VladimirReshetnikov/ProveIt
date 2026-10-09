"""Independent algebraic and graph checks, not a geometric/source-completeness oracle.

The cycle basis is computed by binary nullspace elimination, and exterior
coordinates by direct square determinants. Neither producer implementation is
used. Alternative basis choices preserve linear identities in each grading.
"""
from __future__ import annotations
from collections import Counter
from hashlib import sha256
from itertools import combinations
from math import comb
import json
from typing import Sequence


def _valid(p):
    if not isinstance(p, (list, tuple)) or not p:
        raise ValueError('nonempty partition required')
    seen = set()
    for x in p:
        if type(x) is not int or x < 0 or x > len(seen):
            raise ValueError('invalid restricted-growth partition')
        seen.add(x)
    return tuple(p)


def _blocks(p):
    return [[i for i, x in enumerate(p) if x == b] for b in range(max(p) + 1)]


def _refines(p, q):
    return len(p) == len(q) and all(len({q[i] for i in b}) == 1 for b in _blocks(p))


def components(adjacency):
    unseen = set(range(len(adjacency)))
    result = []
    while unseen:
        first = min(unseen)
        unseen.remove(first)
        found, todo = {first}, [first]
        while todo:
            x = todo.pop()
            for y in adjacency[x]:
                if y not in found:
                    found.add(y)
                    unseen.discard(y)
                    todo.append(y)
        result.append(found)
    return result


def _incidence(sigma, rho):
    s, t = max(sigma) + 1, max(rho) + 1
    rows = [0] * (s + t)
    adj = [set() for _ in rows]
    for e, (u, v) in enumerate(zip(sigma, rho)):
        v += s
        rows[u] |= 1 << e
        rows[v] |= 1 << e
        adj[u].add(v); adj[v].add(u)
    return rows, adj


def nullspace(rows, n):
    """RREF with low-column pivots; returns a basis of the binary nullspace."""
    a = list(rows)
    pivots = []
    rank = 0
    for col in range(n):
        position = next((i for i in range(rank, len(a)) if a[i] >> col & 1), None)
        if position is None:
            continue
        a[rank], a[position] = a[position], a[rank]
        for i in range(len(a)):
            if i != rank and (a[i] >> col & 1):
                a[i] ^= a[rank]
        pivots.append(col)
        rank += 1
    out = []
    for free in range(n):
        if free in pivots:
            continue
        x = 1 << free
        for i, p in enumerate(pivots):
            if a[i] >> free & 1:
                x |= 1 << p
        out.append(x)
    return out


def determinant(rows):
    a = list(rows)
    n = len(a)
    for k in range(n):
        i = next((i for i in range(k, n) if a[i] >> k & 1), None)
        if i is None:
            return 0
        a[k], a[i] = a[i], a[k]
        for i in range(k + 1, n):
            if a[i] >> k & 1:
                a[i] ^= a[k]
    return 1


def _feature(p, coarse, basis):
    """All maximal minors; omit LAST subblock, unlike the producer."""
    rows = []
    for large in _blocks(coarse):
        sub = sorted(set(p[i] for i in large))
        for small in sub[:-1]:
            mask = sum(1 << i for i in large if p[i] == small)
            rows.append(sum((((z & mask).bit_count() & 1) << j) for j, z in enumerate(basis)))
    lam, degree = len(basis), len(rows)
    if degree > lam:
        return 0
    value = 0
    for subset in combinations(range(lam), degree):
        minor = [sum(((row >> col & 1) << j) for j, col in enumerate(subset)) for row in rows]
        if determinant(minor):
            coordinate = sum(1 << col for col in subset)
            value |= 1 << coordinate
    return value


def direct_compatible(p, q):
    p, q = _valid(p), _valid(q)
    if len(p) != len(q):
        return False
    _, adj = _incidence(p, q)
    return len(p) == len(adj) - 1 and len(components(adj)) == 1


def direct_viable(p, rho):
    _, adj = _incidence(p, rho)
    return len(components(adj)) == 1


def root_feature_by_subsets(p):
    bs = _blocks(p)
    value = 0
    for mask in range(1 << (len(p) - 1)):
        chosen = (mask << 1) | 1
        if all(sum(chosen >> i & 1 for i in b) == 1 for b in bs):
            value |= 1 << mask
    return value


def check_reduction(items, sigma, rho, certificate, *, max_dimension=1 << 18):
    """Return (valid, reason); input candidates are supplied independently.

    This verifies the exact algebraic pruning claim, not whether envelopes
    safely contain all future geometric possibilities.
    """
    try:
        sigma, rho = _valid(sigma), _valid(rho)
        if len(sigma) != len(rho):
            raise ValueError('different envelope widths')
        if not isinstance(certificate, dict) or set(certificate) != {
            'schema', 'mode', 'source_sha256', 'retained', 'expansions'}:
            raise ValueError('certificate schema fields disagree')
        if certificate['schema'] != 'cycle-envelope-reduction-v1':
            raise ValueError('unknown schema')
        mode = certificate['mode']
        if mode not in ('cycle', 'root'):
            raise ValueError('unknown mode')
        payload = {'sigma': list(sigma), 'rho': list(rho), 'items': []}
        for c in items:
            p = _valid(c.partition)
            if not _refines(p, sigma) or type(c.cost) is not int or type(c.sector) is not int or not 0 <= c.sector < 4:
                raise ValueError('invalid source candidate')
            if not isinstance(c.witness, tuple) or any(type(x) is not int or x < 0 for x in c.witness):
                raise ValueError('invalid witness path')
            payload['items'].append({'partition': list(p), 'cost_hex': hex(c.cost),
                                     'sector': c.sector, 'witness': list(c.witness)})
        digest = sha256(json.dumps(payload, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        if certificate['source_sha256'] != digest:
            raise ValueError('source binding mismatch')
        kept = certificate['retained']
        expansions = certificate['expansions']
        if not isinstance(kept, list) or any(type(i) is not int or not 0 <= i < len(items) for i in kept):
            raise ValueError('invalid retained indices')
        if len(set(kept)) != len(kept):
            raise ValueError('duplicate retained index')
        if not isinstance(expansions, list) or len(expansions) != len(items):
            raise ValueError('missing expansion')
        incidence, adj = _incidence(sigma, rho)
        connected = len(components(adj)) == 1
        basis = nullspace(incidence, len(sigma)) if connected else []
        lam = len(basis)
        dim = (1 << lam) if mode == 'cycle' else (1 << (len(sigma) - 1))
        if dim > max_dimension:
            raise ValueError('checker allocation guard')
        rows = {}
        for c in items:
            if c.partition not in rows:
                if not connected:
                    rows[c.partition] = 0
                elif mode == 'cycle':
                    rows[c.partition] = _feature(c.partition, sigma, basis)
                else:
                    rows[c.partition] = (root_feature_by_subsets(c.partition)
                                         if direct_viable(c.partition, rho) else 0)
        kept_set = set(kept)
        for i, expansion in enumerate(expansions):
            if not isinstance(expansion, list) or any(type(j) is not int or j not in kept_set for j in expansion):
                raise ValueError('invalid expansion index')
            if len(set(expansion)) != len(expansion):
                raise ValueError('duplicate expansion index')
            value = 0
            for j in expansion:
                if items[j].cost > items[i].cost or items[j].sector != items[i].sector:
                    raise ValueError('cost or sector violation')
                value ^= rows[items[j].partition]
            if value != rows[items[i].partition]:
                raise ValueError('false row identity')
        grades = Counter((items[i].sector, len(set(items[i].partition))) for i in kept)
        for (sector, c), number in grades.items():
            if not connected:
                limit = 0
            elif mode == 'cycle':
                j = c - len(set(sigma))
                limit = comb(lam, j) if 0 <= j <= lam else 0
            else:
                limit = comb(len(sigma) - 1, c - 1)
            if number > limit:
                raise ValueError('graded size bound exceeded')
        return True, 'all source-bound expansions and graded bounds verified'
    except (ValueError, TypeError, KeyError, AttributeError, IndexError) as exc:
        return False, str(exc)


def slow_transition(p, patch, out_width):
    """BFS multigraph replay, independent of the producer's cycle-union test."""
    r = len(p)
    a, b = max(p) + 1, max(patch) + 1
    adj = [set() for _ in range(a + b)]
    edges = []
    for i in range(r):
        u, v = p[i], a + patch[i]
        adj[u].add(v); adj[v].add(u)
        edges.append((u, v))
    cc = components(adj)
    answer = [-1] * out_width
    for group in cc:
        edge_count = sum(u in group for u, _ in edges)
        if edge_count != len(group) - 1:
            return None
        out = [j for j in range(out_width) if a + patch[r + j] in group]
        if not out:
            return None
        for j in out:
            answer[j] = min(out)
    names = {}
    return tuple(names.setdefault(x, len(names)) for x in answer)


def universal_envelopes(g):
    """Independent whole-prefix/suffix graph construction, deliberately simple."""
    offsets, total = [], 0
    for r in g.widths:
        offsets.append(total)
        total += r
    def connect(adj, p, labels):
        for b in _blocks(p):
            for i in b[1:]:
                x, y = labels[b[0]], labels[i]
                adj[x].add(y); adj[y].add(x)
    def restricted(adj, cut):
        colors = {}
        for group in components(adj):
            for v in group:
                colors[v] = min(group)
        names = {}
        return tuple(names.setdefault(colors[v], len(names)) for v in cut)
    past, future = [], []
    for i, r in enumerate(g.widths):
        pa = [set() for _ in range(total)]
        fu = [set() for _ in range(total)]
        for c in g.initial:
            connect(pa, c.partition, list(range(g.widths[0])))
        for c in g.caps:
            connect(fu, c.partition, list(range(offsets[-1], total)))
        for j, layer in enumerate(g.layers):
            labels = list(range(offsets[j], offsets[j + 1] + g.widths[j + 1]))
            for p in layer:
                connect(pa if j < i else fu, p.partition, labels)
        cut = list(range(offsets[i], offsets[i] + r))
        past.append(restricted(pa, cut)); future.append(restricted(fu, cut))
    return tuple(past), tuple(future)


def check_run(g, result):
    """Replay every option, pruning proof, and final optimum inside this grammar.

    Uses independent graph connectivity/transition code. Shared dataclasses are
    data containers only. Does not assert ambient embedding or knot completeness.
    """
    from envelope_kernel import Candidate
    from grammar import digest
    try:
        if not isinstance(result, dict) or set(result) != {
            'schema', 'grammar_sha256', 'mode', 'status', 'cost_hex', 'witness',
            'sector', 'stages', 'statistics'}:
            raise ValueError('invalid run schema')
        if result['schema'] != 'cycle-envelope-run-v1' or result['grammar_sha256'] != digest(g):
            raise ValueError('grammar binding mismatch')
        mode = result['mode']
        if mode not in ('exact', 'root', 'cycle') or len(result['stages']) != len(g.widths):
            raise ValueError('invalid run mode or stage count')
        sigma, rho = universal_envelopes(g)
        items = [Candidate(c.partition, c.cost, c.sector, (j,)) for j, c in enumerate(g.initial)]
        expected_stats = []
        for i in range(len(g.widths)):
            raw = len(items)
            best = {}
            for c in items:
                key = (c.partition, c.sector)
                if key not in best or (c.cost, c.witness) < (best[key].cost, best[key].witness):
                    best[key] = c
            items = [best[key] for key in sorted(best) if direct_viable(best[key].partition, rho[i])]
            before = len(items)
            cert = result['stages'][i]
            if mode == 'exact':
                if cert != {'schema': 'exact-dedup-v1', 'retained': list(range(len(items)))}:
                    raise ValueError('invalid exact-mode retained list')
            else:
                if cert.get('mode') != mode:
                    raise ValueError('stage mode mismatch')
                ok, reason = check_reduction(items, sigma[i], rho[i], cert)
                if not ok:
                    raise ValueError('stage ' + str(i) + ': ' + reason)
                items = [items[j] for j in cert['retained']]
            incidence, adj = _incidence(sigma[i], rho[i])
            lam = g.widths[i] + 1 - len(adj) if len(components(adj)) == 1 else None
            expected_stats.append({'interface': i, 'arcs': g.widths[i], 'cycle_rank': lam,
                                   'generated': raw, 'viable_distinct': before, 'retained': len(items)})
            if i < len(g.layers):
                following = []
                for c in items:
                    for j, option in enumerate(g.layers[i]):
                        p = slow_transition(c.partition, option.partition, g.widths[i + 1])
                        if p is not None:
                            following.append(Candidate(p, c.cost + option.cost,
                                c.sector ^ option.sector, c.witness + (j,)))
                items = following
        answers = []
        for c in items:
            for j, cap in enumerate(g.caps):
                if (c.sector ^ cap.sector in g.target_sectors and
                    direct_compatible(c.partition, cap.partition)):
                    answers.append((c.cost + cap.cost, c.witness + (j,), c.sector ^ cap.sector))
        best = min(answers) if answers else None
        expected = ('NO_DISK_IN_GRAMMAR', None, None, None) if best is None else (
            'FOUND_ABSTRACT_DISK', hex(best[0]), list(best[1]), best[2])
        if (result['status'], result['cost_hex'], result['witness'], result['sector']) != expected:
            raise ValueError('wrong terminal optimum or witness')
        if result['statistics'] != expected_stats:
            raise ValueError('incorrect work statistics')
        return True, 'all source options, reductions, and terminal queries replayed'
    except (ValueError, TypeError, KeyError, AttributeError, IndexError) as exc:
        return False, str(exc)
