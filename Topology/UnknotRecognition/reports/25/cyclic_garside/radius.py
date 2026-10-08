"""Exact cyclic compression with a finite word-ball target dictionary.

Input-prefix states are shared across cuts. A trie of inverse target words also
shares target arithmetic at each endpoint. The dictionary is exponential in the
chosen radius; no bound independent of radius is claimed. Radius two is intended
as an optional research probe, not a replacement for cheaper upstream stages.
"""
from __future__ import annotations
from bisect import bisect_left
from dataclasses import asdict
from itertools import product
from .normalform import IDENTITY, Counters, LimitExceeded, append, normal_form, validate
from .kernel import input_digest, length_lower_bound


def _dictionary(b, radius, max_targets):
    alphabet = tuple(a for i in range(1, b) for a in (i, -i))
    count, level = 1, 1
    for _ in range(radius):
        level *= len(alphabet)
        count += level
        if max_targets is not None and count > max_targets:
            raise LimitExceeded(f"target dictionary exceeds allowance {max_targets}")
    return [()] + [w for d in range(1, radius+1) for w in product(alphabet, repeat=d)]


def _trie(targets):
    """Deterministic lexicographic trie, returned in depth-first preorder.

    Each node: (depth, incoming letter, target index or -1). No hash table.
    The root is implicit. Parent states are available on a depth stack.
    """
    items = sorted((tuple(-a for a in reversed(v)), i) for i, v in enumerate(targets))
    nodes, path, previous = [[0, 0, -1]], [0], ()
    for word, index in items:
        common = 0
        while common < min(len(previous), len(word)) and previous[common] == word[common]:
            common += 1
        path = path[:common+1]
        for depth in range(common+1, len(word)+1):
            nodes.append([depth, word[depth-1], -1])
            path.append(len(nodes)-1)
        nodes[path[-1]][2] = index
        previous = word
    return nodes


def _prepare_radius(b, word, cyclic, targets, nodes, counters, budget):
    source = word+word if cyclic else word
    states = [IDENTITY]
    for a in source:
        state, _ = append(states[-1], a, b, counters=counters, budget=budget)
        states.append(state)
    counters.prefix_height = max((len(s[1]) for s in states), default=0)
    unique = []
    for state in sorted(states):
        if not unique or state != unique[-1]:
            unique.append(state)
    ids = [bisect_left(unique, s) for s in states]
    queries = [None]*len(states)
    for j in range(1, len(states)):
        if budget:
            budget.check()
        row = [-1]*len(targets)
        stack = [states[j]]
        if nodes[0][2] >= 0:
            row[nodes[0][2]] = ids[j]
        for depth, letter, terminal in nodes[1:]:
            stack = stack[:depth]
            state, _ = append(stack[-1], letter, b, counters=counters, budget=budget)
            stack.append(state)
            if terminal >= 0:
                pos = bisect_left(unique, state)
                row[terminal] = pos if pos < len(unique) and unique[pos] == state else -1
        queries[j] = row
    return ids, queries, len(unique)


def _solve_radius(n, cut, ids, queries, targets, count, budget):
    scores, starts = [-10*(n+1)]*count, [-1]*count
    scores[ids[cut]], starts[ids[cut]] = 0, 0
    best = [0]*(n+1)
    previous = [(0, -1)]*(n+1)
    checks = 0
    for j in range(1, n+1):
        if budget:
            budget.check()
        value, choice = best[j-1], (j-1, -1)
        for t, (target, key) in enumerate(zip(targets, queries[cut+j])):
            checks += 1
            if key < 0 or starts[key] < 0:
                continue
            candidate = j-len(target)+scores[key]
            if candidate > value:
                value, choice = candidate, (starts[key], t)
        best[j], previous[j] = value, choice
        key = ids[cut+j]
        candidate = value-j
        if candidate > scores[key]:
            scores[key], starts[key] = candidate, j
    plan, j = [], n
    while j:
        i, target = previous[j]
        if target >= 0:
            plan.append((i, j, targets[target]))
        j = i
    return n-best[n], list(reversed(plan)), checks


def compress_radius(b, word, *, radius=2, cyclic=True, stop_at_lower_bound=True,
                    max_targets=100000, budget=None):
    """Optimal one-pass replacements by words of length at most `radius`.

    A local dictionary/operation limit raises LimitExceeded, never a knot verdict.
    Set max_targets=None to remove the dictionary cap in the theoretical route.
    The result carries a version-2 residual-word replay certificate.
    """
    word = validate(b, word)
    if type(radius) is not int or radius < 1:
        raise ValueError("radius must be a positive integer")
    if max_targets is not None and (type(max_targets) is not int or max_targets < 1):
        raise ValueError("max_targets must be a positive integer or None")
    n, lower = len(word), length_lower_bound(b, word)
    counters = Counters()
    best, cut, plan, checks, rotations, target_count, trie_nodes = n, 0, [], 0, 0, 0, 0
    if n and not (stop_at_lower_bound and lower == n):
        targets = _dictionary(b, radius, max_targets)
        nodes = _trie(targets)
        target_count, trie_nodes = len(targets), len(nodes)
        ids, queries, count = _prepare_radius(b, word, cyclic, targets, nodes, counters, budget)
        for s in range(n if cyclic else 1):
            value, candidate, work = _solve_radius(n, s, ids, queries, targets, count, budget)
            checks += work
            rotations += 1
            if value < best:
                best, cut, plan = value, s, candidate
            if stop_at_lower_bound and best == lower:
                break
    algebra_appends = counters.appends
    rotated = word[cut:]+word[:cut]
    output, records, end = [], [], 0
    for i, j, target in plan:
        output.extend(rotated[end:i])
        output.extend(target)
        residual = rotated[i:j] + tuple(-a for a in reversed(target))
        state, proof = normal_form(b, residual, trace=True, counters=counters, budget=budget)
        assert state == IDENTITY
        records.append(dict(start=i, end=j, target=list(target), proof=proof))
        end = j
    output.extend(rotated[end:])
    assert len(output) == best
    certificate = dict(schema="cyclic-garside-kernel-v2", strands=b,
                       input_digest=input_digest(b, word), mode="cyclic" if cyclic else "linear",
                       rotation=cut, output=output, replacements=records, target_radius=radius)
    stats = asdict(counters)
    stats.update(input_length=n, output_length=best, lower_bound=lower,
                 lower_bound_attained=best==lower, rotations_evaluated=rotations,
                 dp_target_checks=checks, target_count=target_count, trie_nodes=trie_nodes,
                 algebra_appends_before_proof=algebra_appends)
    return dict(word=output, certificate=certificate, stats=stats)
