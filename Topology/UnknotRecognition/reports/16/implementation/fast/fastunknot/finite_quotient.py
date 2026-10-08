"""Exact, budgeted nonabelian A5 representation filter for fastunknot.

The only knot verdict is backed by an explicit permutation certificate.  An
exhausted palette or resource budget is always INCONCLUSIVE, never UNKNOT.
This module intentionally does not modify the existing recognition pipeline.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import time
from collections import deque
from functools import lru_cache


def _compose(a, b):
    """a after b, with permutations encoded as image tuples of 0,...,4."""
    return tuple(a[b[i]] for i in range(5))


def _inverse(a):
    result = [0] * 5
    for i, j in enumerate(a):
        result[j] = i
    return tuple(result)


def _conjugate(a, b):
    return _compose(_compose(a, b), _inverse(a))


def _even(a):
    return sum(a[i] > a[j] for i in range(5) for j in range(i + 1, 5)) % 2 == 0


def pd_digest(diagram):
    return hashlib.sha256(json.dumps(diagram.pd, separators=(",", ":")).encode()).hexdigest()


@lru_cache(maxsize=3)
def _palette(order):
    seeds = {2: (1, 0, 3, 2, 4), 3: (1, 2, 0, 3, 4), 5: (1, 2, 3, 4, 0)}
    if order not in seeds:
        raise ValueError("A5 meridian orders must be 2, 3, or 5")
    group = tuple(p for p in itertools.permutations(range(5)) if _even(p))
    seed = seeds[order]
    colors = tuple(sorted({_conjugate(g, seed) for g in group}))
    index = {p: i for i, p in enumerate(colors)}
    tables = {}
    for sign in (-1, 1):
        tables[sign] = tuple(tuple(index[_conjugate(g if sign == 1 else _inverse(g), u)]
                                   for u in colors) for g in colors)
    stabilizer = tuple(tuple(index[_conjugate(g, x)] for x in colors)
                       for g in group if _conjugate(g, colors[0]) == colors[0])
    return colors, tables, stabilizer


def wirtinger_data(diagram):
    """Return edge->arc map and (over,incoming_under,outgoing_under,sign)."""
    n = diagram.crossings
    if n == 0:
        return [], []
    parent = list(range(2 * n))

    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for _, b, _, d in diagram.pd:
        parent[root(d)] = root(b)
    roots = sorted({root(e) for e in range(2 * n)})
    labels = {r: i for i, r in enumerate(roots)}
    owner = [labels[root(e)] for e in range(2 * n)]
    if len(roots) != n:
        raise ArithmeticError("expected n Wirtinger arcs in a nonempty knot diagram")
    incoming = diagram.incoming_slots()
    signs = diagram.signs()
    relations = []
    for k, row in enumerate(diagram.pd):
        slot = incoming[k][0]
        relations.append((owner[row[1]], owner[row[slot]], owner[row[(slot + 2) % 4]],
                          signs[k]))
    return owner, relations


class _Relation:
    """Small extensional relation, represented by Python integer bitsets."""
    def __init__(self, table, pattern, q):
        self.q = q
        self.arity = len(set(pattern))
        self.supports = [[0] * q for _ in range(self.arity)]
        count = 0
        for a in range(q):
            for b in range(q):
                triple = (a, b, table[a][b])
                values = [None] * self.arity
                for slot, value in zip(pattern, triple):
                    if values[slot] is not None and values[slot] != value:
                        break
                    values[slot] = value
                else:
                    bit = 1 << count
                    for i, value in enumerate(values):
                        self.supports[i][value] |= bit
                    count += 1
        self.full = (1 << count) - 1
        self.expansions = [{} for _ in range(self.arity)]

    def cover(self, position, domain):
        cache = self.expansions[position]
        if domain not in cache:
            result, remaining = 0, domain
            while remaining:
                bit = remaining & -remaining
                result |= self.supports[position][bit.bit_length() - 1]
                remaining ^= bit
            cache[domain] = result
        return cache[domain]


def _orbit_representatives(domain, stabilizer):
    remaining = domain
    while remaining:
        bit = remaining & -remaining
        color = bit.bit_length() - 1
        yield color
        orbit = 0
        for action in stabilizer:
            orbit |= 1 << action[color]
        remaining &= ~orbit


def _solve(relations, q, tables, stabilizer, *, max_nodes, deadline, stats):
    n = len(relations)
    full_domain = (1 << q) - 1
    constraints = []
    templates = {}
    incident = [[] for _ in range(n)]
    for o, u, v, sign in relations:
        scope = tuple(dict.fromkeys((o, u, v)))
        pattern = tuple(scope.index(x) for x in (o, u, v))
        key = sign, pattern
        if key not in templates:
            templates[key] = _Relation(tables[sign], pattern, q)
        k = len(constraints)
        constraints.append((scope, templates[key]))
        for x in scope:
            incident[x].append(k)

    def check_budget():
        if max_nodes is not None and stats["nodes"] >= max_nodes:
            raise _Limit("node budget exhausted")
        if deadline is not None and time.monotonic() >= deadline:
            raise _Limit("time budget exhausted")

    def propagate(domains, active):
        queue = deque(range(len(constraints)))
        pending = set(queue)
        while queue:
            if deadline is not None and stats["propagations"] % 64 == 0:
                if time.monotonic() >= deadline:
                    raise _Limit("time budget exhausted")
            k = queue.popleft()
            pending.discard(k)
            scope, relation = constraints[k]
            mask = active[k]
            for position, var in enumerate(scope):
                mask &= relation.cover(position, domains[var])
            if not mask:
                return False
            active[k] = mask
            stats["propagations"] += 1
            for position, var in enumerate(scope):
                supported, remaining = 0, domains[var]
                while remaining:
                    bit = remaining & -remaining
                    if relation.supports[position][bit.bit_length() - 1] & mask:
                        supported |= bit
                    remaining ^= bit
                if supported != domains[var]:
                    domains[var] = supported
                    for other in incident[var]:
                        if other not in pending:
                            queue.append(other)
                            pending.add(other)
        # Since arc zero is anchored at color zero, exclude the constant map.
        possible = [i for i, domain in enumerate(domains) if domain & ~1]
        if not possible:
            return False
        if len(possible) == 1 and domains[possible[0]] & 1:
            domains[possible[0]] &= ~1
            return propagate(domains, active)
        return True

    def search(domains, active, symmetry):
        # Explicit stack: a large input cannot overflow Python's call stack.
        stack = [(domains, active, symmetry, 0)]
        while stack:
            domains, active, symmetry, depth = stack.pop()
            check_budget()
            stats["nodes"] += 1
            stats["max_depth"] = max(stats["max_depth"], depth)
            if not propagate(domains, active):
                stats["contradictions"] += 1
                continue
            candidates = [v for v, d in enumerate(domains) if d.bit_count() > 1]
            if not candidates:
                return [d.bit_length() - 1 for d in domains]
            var = min(candidates, key=lambda v: (domains[v].bit_count(), -len(incident[v]), v))
            representatives = list(_orbit_representatives(domains[var], symmetry))
            for color in reversed(representatives):
                child = list(domains)
                child[var] = 1 << color
                subgroup = tuple(action for action in symmetry if action[color] == color)
                stack.append((child, list(active), subgroup, depth + 1))
        return None

    domains = [full_domain] * n
    domains[0] = 1
    return search(domains, [relation.full for _, relation in constraints], stabilizer)


class _Limit(Exception):
    pass


def _make_certificate(diagram, owner, colors, assignment):
    edge_images = [colors[assignment[a]] for a in owner]
    pair = next(((0, j) for j in range(1, len(edge_images))
                 if _compose(edge_images[0], edge_images[j]) !=
                 _compose(edge_images[j], edge_images[0])), None)
    if pair is None:
        raise ArithmeticError("nonconstant knot coloring has no noncommuting pair")
    certificate = {"schema": "fastunknot-a5-wirtinger-v1", "pd_sha256": pd_digest(diagram),
                   "edge_images": [list(p) for p in edge_images],
                   "noncommuting_edges": list(pair)}
    if __package__:
        from .finite_quotient_check import verify_certificate
    else:
        from finite_quotient_check import verify_certificate
    checked = verify_certificate(diagram.pd, certificate)
    if not checked["valid"]:
        raise ArithmeticError("internal certificate failure: " + checked["reason"])
    return certificate


def find_a5_certificate(diagram, *, classes=(3, 2, 5), max_nodes=10000, seconds=None):
    """Search selected A5 meridian classes; replay is mandatory before verdict.

    ``max_nodes`` bounds recursive CSP nodes *across all classes*.  ``seconds``
    is a cooperative wall-clock budget, checked in search and propagation; it
    does not promise a hard process interruption.  Both may be None.  The
    order-five class omitted from the palette is carried to the searched class
    by conjugation in S5, an automorphism of A5.
    """
    started = time.monotonic()
    if max_nodes is not None and (type(max_nodes) is not int or max_nodes < 0):
        raise ValueError("max_nodes must be a nonnegative integer or None")
    if seconds is not None and seconds < 0:
        raise ValueError("seconds must be nonnegative or None")
    classes = tuple(classes)
    if any(order not in (2, 3, 5) for order in classes):
        raise ValueError("A5 meridian orders must be 2, 3, or 5")
    deadline = None if seconds is None else started + seconds
    owner, relations = wirtinger_data(diagram)
    total = {"nodes": 0, "propagations": 0, "contradictions": 0, "max_depth": 0}
    attempts = []
    result = {"status": "INCONCLUSIVE", "reason": "selected A5 palette exhausted",
              "certificate": None, "attempts": attempts, "stats": total}
    for order in classes if relations else ():
        if deadline is not None and time.monotonic() >= deadline:
            result["reason"] = "time budget exhausted"
            break
        colors, tables, stabilizer = _palette(order)
        stats = {"nodes": 0, "propagations": 0, "contradictions": 0, "max_depth": 0}
        try:
            left = None if max_nodes is None else max_nodes - total["nodes"]
            assignment = _solve(relations, len(colors), tables, stabilizer,
                                max_nodes=left, deadline=deadline, stats=stats)
        except _Limit as exc:
            assignment = None
            result["reason"] = str(exc)
        attempts.append({"meridian_order": order, "class_size": len(colors), **stats})
        for key in total:
            total[key] = max(total[key], stats[key]) if key == "max_depth" else total[key] + stats[key]
        if assignment is not None:
            # Independent edge-level checker; it uses no CSP tables or arc map.
            certificate = _make_certificate(diagram, owner, colors, assignment)
            result.update(status="KNOTTED", reason="verified nonabelian A5 representation",
                          certificate=certificate)
            break
        if result["reason"] != "selected A5 palette exhausted":
            break
    if not relations:
        result["reason"] = "crossing-free diagram; no nonabelian representation"
    result["seconds"] = time.monotonic() - started
    return result


def wirtinger_seed_plan(diagram, *, check=lambda: None):
    """Greedily find a generating seed set under forced Wirtinger propagation.

    The result certifies an upper bound on seed number, not its minimum.  A
    supplied plan needs no knot invariant computation: check that every target
    is a previously unknown under-arc with its over and other under-arc known.
    """
    owner, relations = wirtinger_data(diagram)
    n = len(relations)
    if n == 0:
        return {"seed_arcs": [], "steps": [], "edge_arcs": owner, "arcs": 0}
    incident = [[] for _ in range(n)]
    for k, (o, u, v, _) in enumerate(relations):
        for arc in set((o, u, v)):
            incident[arc].append(k)

    def closure(seeds):
        check()
        known = set(seeds)
        queue = deque(seeds)
        steps = []
        while queue:
            arc = queue.popleft()
            for k in incident[arc]:
                o, u, v, _ = relations[k]
                if o in known and ((u in known) != (v in known)):
                    target = v if u in known else u
                    known.add(target)
                    queue.append(target)
                    steps.append({"crossing": k, "target_arc": target})
        return known, steps

    seeds = [0]
    known, steps = closure(seeds)
    while len(known) < n:
        next_arc = max((i for i in range(n) if i not in known),
                       key=lambda i: (len(closure(seeds + [i])[0]), -i))
        seeds.append(next_arc)
        known, steps = closure(seeds)
    return {"seed_arcs": seeds, "steps": steps, "edge_arcs": owner, "arcs": n}


def _seed_assignments(q, count, stabilizer):
    """One representative per simultaneous-conjugation orbit of seed tuples."""
    stack = [((), stabilizer)]
    while stack:
        prefix, symmetry = stack.pop()
        if len(prefix) == count:
            yield prefix
            continue
        representatives = list(_orbit_representatives((1 << q) - 1, symmetry))
        for color in reversed(representatives):
            subgroup = tuple(action for action in symmetry if action[color] == color)
            stack.append((prefix + (color,), subgroup))


def a5_seed_orbit_count(order, seeds):
    """Exact number of seed-tuple orbits after anchoring the first meridian.

    Burnside's lemma for centralizers V4, C3, C5, respectively.  Nonidentity
    elements fix 3, 2, 2 colors in the selected conjugacy classes.
    """
    if type(seeds) is not int or seeds < 1:
        raise ValueError("seeds must be a positive integer")
    r = seeds - 1
    if order == 2:
        return (15 ** r + 3 * 3 ** r) // 4
    if order == 3:
        return (20 ** r + 2 * 2 ** r) // 3
    if order == 5:
        return (12 ** r + 4 * 2 ** r) // 5
    raise ValueError("A5 meridian orders must be 2, 3, or 5")


def find_a5_by_seeds(diagram, *, classes=(3, 2, 5), max_assignments=100000, seconds=None,
                     symmetry=True):
    """Exhaustive fixed-seed solver with O(n q**(b-1)) coloring work per class.

    For a plan of b seeds, all n colors are forced by the b seed colors.  Global
    conjugation fixes the first seed, so exactly q**(b-1) candidates suffice.
    Greedy plan construction costs O(n**3) and does not establish minimality.
    A budget can stop enumeration, in which case only INCONCLUSIVE is returned.
    """
    started = time.monotonic()
    if max_assignments is not None and (type(max_assignments) is not int or max_assignments < 0):
        raise ValueError("max_assignments must be a nonnegative integer or None")
    if seconds is not None and seconds < 0:
        raise ValueError("seconds must be nonnegative or None")
    classes = tuple(classes)
    if any(order not in (2, 3, 5) for order in classes):
        raise ValueError("A5 meridian orders must be 2, 3, or 5")
    deadline = None if seconds is None else started + seconds
    owner, relations = wirtinger_data(diagram)
    result = {"status": "INCONCLUSIVE", "reason": "selected A5 palette exhausted",
              "certificate": None, "plan": None, "assignments": 0, "attempts": []}

    def check():
        if deadline is not None and time.monotonic() >= deadline:
            raise _Limit("time budget exhausted")

    try:
        check()
        plan = wirtinger_seed_plan(diagram, check=check)
    except _Limit as exc:
        result["reason"] = str(exc)
        result["seconds"] = time.monotonic() - started
        return result
    result["plan"] = plan
    n, seeds = len(relations), plan["seed_arcs"]
    for order in classes if n else ():
        colors, tables, stabilizer = _palette(order)
        q = len(colors)
        attempt = {"meridian_order": order, "class_size": q,
                   "exhaustive_assignment_bound": q ** (len(seeds) - 1),
                   "orbit_assignment_bound": (a5_seed_orbit_count(order, len(seeds)) if symmetry
                                                else q ** (len(seeds) - 1)),
                   "assignments": 0}
        result["attempts"].append(attempt)
        candidates = (_seed_assignments(q, len(seeds) - 1, stabilizer) if symmetry
                      else itertools.product(range(q), repeat=len(seeds) - 1))
        for free in candidates:
            if max_assignments is not None and result["assignments"] >= max_assignments:
                result["reason"] = "assignment budget exhausted"
                break
            if deadline is not None and time.monotonic() >= deadline:
                result["reason"] = "time budget exhausted"
                break
            result["assignments"] += 1
            attempt["assignments"] += 1
            assignment = [None] * n
            for arc, color in zip(seeds, (0,) + free):
                assignment[arc] = color
            for step in plan["steps"]:
                o, u, v, sign = relations[step["crossing"]]
                target = step["target_arc"]
                assignment[target] = (tables[sign][assignment[o]][assignment[u]] if target == v
                                      else tables[-sign][assignment[o]][assignment[v]])
            if not any(assignment):
                continue
            if all(tables[s][assignment[o]][assignment[u]] == assignment[v]
                   for o, u, v, s in relations):
                certificate = _make_certificate(diagram, owner, colors, assignment)
                result.update(status="KNOTTED", reason="verified nonabelian A5 representation",
                              certificate=certificate)
                break
        if result["reason"] != "selected A5 palette exhausted":
            break
    if not n:
        result["reason"] = "crossing-free diagram; no nonabelian representation"
    result["seconds"] = time.monotonic() - started
    return result


def main():
    import argparse
    from fastunknot import Diagram
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    parser.add_argument("--solver", choices=("seeds", "csp"), default="seeds")
    parser.add_argument("--max-nodes", type=int, default=10000)
    parser.add_argument("--max-assignments", type=int, default=100000)
    parser.add_argument("--seconds", type=float)
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as handle:
        diagram = Diagram.from_json(json.load(handle))
    result = (find_a5_by_seeds(diagram, max_assignments=args.max_assignments, seconds=args.seconds)
              if args.solver == "seeds" else
              find_a5_certificate(diagram, max_nodes=args.max_nodes, seconds=args.seconds))
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "KNOTTED" else 3


if __name__ == "__main__":
    raise SystemExit(main())
