"""Independent deterministic certificate replay. Imports no producer or algebra.

A valid local certificate does not authenticate the geometric source and is not
an unknot/knottedness certificate. The input has boundary root normalized to 0.
"""
from __future__ import annotations
import hashlib
import json


def _digest(inst) -> str:
    data = [inst.vertices, inst.columns, inst.edges,
            [[hex(x) for x in row] for row in inst.matrix]]
    return hashlib.sha256(json.dumps(data, separators=(',', ':')).encode()).hexdigest()


def _partition_rank(n, pairs):
    components = [{v} for v in range(n)]
    rank = 0
    for u, v in pairs:
        a = next(i for i, c in enumerate(components) if u in c)
        b = next(i for i, c in enumerate(components) if v in c)
        if a != b:
            components[a] |= components[b]
            components.pop(b)
            rank += 1
    return rank


def verify_positive(inst, certificate: dict) -> bool:
    try:
        if type(certificate) is not dict or certificate.get('schema') != 'activation-forest-positive-v1':
            return False
        if certificate['input_sha256'] != _digest(inst):
            return False
        tree = certificate['tree']
        if type(tree) is not list or any(type(e) is not int or not 0 <= e < inst.m for e in tree):
            return False
        if len(tree) != inst.vertices - 1 or len(set(tree)) != len(tree):
            return False
        if _partition_rank(inst.vertices, (inst.edges[e] for e in tree)) != len(tree):
            return False
        exposed = {0}
        deleted = set()
        for move in certificate['dual_order']:
            if type(move) is not list or len(move) != 2:
                return False
            e, child = move
            if type(e) is not int or type(child) is not int or e not in tree or e in deleted:
                return False
            u, v = inst.edges[e]
            if child in exposed or not ((u in exposed and v == child) or (v in exposed and u == child)):
                return False
            exposed.add(child)
            deleted.add(e)
        if deleted != set(tree) or len(exposed) != inst.vertices:
            return False
        live = set(range(inst.m)) - set(tree)
        used_columns = set()
        for move in certificate['pivots']:
            if type(move) is not list or len(move) != 2:
                return False
            row, col = move
            if type(row) is not int or type(col) is not int or row not in live or not 0 <= col < inst.columns or col in used_columns:
                return False
            if inst.matrix[row][col] != 1:
                return False
            if any(inst.matrix[e][col] != 0 for e in live if e != row):
                return False
            live.remove(row)
            used_columns.add(col)
        return not live
    except (KeyError, IndexError, TypeError, ValueError, StopIteration):
        return False


def _mandatory_parts(inst):
    """Independent list/set reconstruction, not the producer's bit-mask closure."""
    adjacency = [set() for _ in range(inst.m)]
    anchors, exceptional = set(), set()
    for col in range(inst.columns):
        support = {e for e in range(inst.m) if inst.matrix[e][col] > 0}
        targets = {e for e in support if inst.matrix[e][col] == 1}
        if not targets:
            continue
        if len(support) == 1:
            anchors |= targets
        elif len(support) == 2:
            for target in targets:
                source = next(iter(support - {target}))
                adjacency[source].add(target)
        else:
            exceptional |= support
    reach = []
    for e in range(inst.m):
        known, stack = {e}, [e]
        while stack:
            for f in adjacency[stack.pop()]:
                if f not in known:
                    known.add(f)
                    stack.append(f)
        reach.append(known)
    parts = {frozenset(f for f in reach[e] if e in reach[f]) for e in range(inst.m)}
    return {part for part in parts if not (part & (anchors | exceptional))
            and not any(adjacency[e] & part for e in range(inst.m) if e not in part)}


def verify_obstruction(inst, certificate: dict) -> bool:
    """Exact obstruction to a successful forest in this FIXED local model only."""
    try:
        if type(certificate) is not dict or inst.m == 0:
            return False
        if certificate.get('schema') == 'activation-frontier-obstruction-v1':
            return verify_frontier(inst, certificate)
        if certificate.get('schema') != 'activation-mandatory-obstruction-v1':
            return False
        if certificate['input_sha256'] != _digest(inst):
            return False
        raw = certificate['blocks']
        if type(raw) is not list or any(type(x) is not list for x in raw):
            return False
        for block in raw:
            if any(type(e) is not int or not 0 <= e < inst.m for e in block) or len(block) != len(set(block)):
                return False
        chosen = {frozenset(x) for x in raw}
        if len(chosen) != len(raw) or not chosen <= _mandatory_parts(inst):
            return False
        union = set().union(set(), *chosen)
        return len(chosen) > _partition_rank(inst.vertices, (inst.edges[e] for e in union))
    except (KeyError, IndexError, TypeError, ValueError, StopIteration):
        return False


def verify_frontier(inst, certificate: dict) -> bool:
    """Independent complete negative replay for q=0 and r<=b only.

    Exterior coordinates are recomputed by binary determinants of source graph
    minors, not by the producer's incremental wedge routine. Source activation
    is recomputed by literal static peeling, not the producer's Horn masks.
    """
    from itertools import combinations
    try:
        if certificate['schema'] != 'activation-frontier-obstruction-v1' or certificate['input_sha256'] != _digest(inst):
            return False
        if _mandatory_parts(inst):
            return False
        boundary = set()
        for h in range(inst.columns):
            support = {e for e in range(inst.m) if inst.matrix[e][h]}
            if len(support) >= 3 and any(inst.matrix[e][h] == 1 for e in support):
                boundary |= support
        boundary = sorted(boundary)
        b, r = len(boundary), inst.vertices - 1
        if r > b:
            return False
        full = (1 << b) - 1
        cache = {}

        def activate(initial):
            key = frozenset(initial)
            if key in cache:
                return cache[key]
            gone = set(key)
            while True:
                before = len(gone)
                for h in range(inst.columns):
                    live = [e for e in range(inst.m) if e not in gone and inst.matrix[e][h]]
                    if len(live) == 1 and inst.matrix[live[0]][h] == 1:
                        gone.add(live[0])
                if len(gone) == before:
                    answer = sum(1 << j for j, e in enumerate(boundary) if e in gone)
                    cache[key] = answer
                    return answer

        wedge_cache = {}

        def minors(chosen):
            key = tuple(chosen)
            if key in wedge_cache:
                return wedge_cache[key]
            k = len(key)
            out = 0
            for index, coordinates in enumerate(combinations(range(1, r + 1), k)):
                rows = []
                for v in coordinates:
                    rows.append(sum(((int(inst.edges[e][0] == v) ^ int(inst.edges[e][1] == v)) << j)
                                    for j, e in enumerate(key)))
                pivots = {}
                for value in rows:
                    while value:
                        lead = value.bit_length() - 1
                        if lead not in pivots:
                            pivots[lead] = value
                            break
                        value ^= pivots[lead]
                if len(pivots) == k:
                    out |= 1 << index
            wedge_cache[key] = out
            return out

        def in_span(value, basis):
            while value:
                lead = value.bit_length() - 1
                if lead not in basis:
                    return False
                value ^= basis[lead]
            return True

        states = {}
        for node in certificate['frontier']:
            mask, k, seeds = node['mask'], node['size'], node['seeds']
            if type(mask) is not int or type(k) is not int or not 0 <= mask < full or not 0 <= k <= r:
                return False
            if (mask, k) in states or type(seeds) is not list or not seeds:
                return False
            basis = {}
            for chosen in seeds:
                if type(chosen) is not list or len(chosen) != k or len(set(chosen)) != k:
                    return False
                if any(type(e) is not int or not 0 <= e < inst.m for e in chosen):
                    return False
                value = minors(chosen)
                if not value or activate(chosen) != mask:
                    return False
                reduced = value
                while reduced:
                    lead = reduced.bit_length() - 1
                    if lead not in basis:
                        basis[lead] = reduced
                        break
                    reduced ^= basis[lead]
                if not reduced:  # Bound the packet by a genuine basis at each state.
                    return False
            states[mask, k] = (seeds, basis)
        initial = activate(())
        if (initial, 0) not in states or not in_span(1, states[initial, 0][1]):
            return False
        for (mask, k), (seeds, basis) in states.items():
            if k == r:
                continue
            abstract_deleted = {boundary[j] for j in range(b) if mask >> j & 1}
            for chosen in seeds:
                for e in range(inst.m):
                    target = activate(abstract_deleted | {e})
                    if target == mask:
                        continue
                    value = minors([*chosen, e])
                    if not value:
                        continue
                    if (target, k + 1) not in states:
                        return False
                    if not in_span(value, states[target, k + 1][1]):
                        return False
        return True
    except (KeyError, IndexError, TypeError, ValueError, StopIteration):
        return False
