"""Independent graph replay for quotient and threshold certificates.

This module imports neither the incremental quotient engine nor the grammar
producer. A source-bound Profiles table must first be authenticated separately.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from collections import defaultdict
from .profiles import Profiles, exact_int


def graph_quotient(profiles, cones):
    """Reconstruct the quotient by an explicit graph on types and active atoms."""
    m, s = len(profiles.lengths), len(profiles.rows)
    graph = {}
    active = set()
    def edge(x, y):
        graph.setdefault(x, set()).add(y)
        graph.setdefault(y, set()).add(x)
    for group in cones:
        group = tuple(group)
        if any(type(j) is not int or not 0 <= j < m for j in group):
            raise ValueError('invalid quotient atom')
        active.update(group)
        if group:
            graph.setdefault(s + group[0], set())
        for j in group[1:]:
            edge(s + group[0], s + j)
    touched = set()
    for i, row in enumerate(profiles.rows):
        for j in active:
            if row.counts[j]:
                touched.add(i)
                edge(i, s + j)
    out = defaultdict(int)
    for i, row in enumerate(profiles.rows):
        if i not in touched:
            out[row.counts] += row.multiplicity
    seen = set()
    for v in graph:
        if v in seen:
            continue
        stack, mass, nonempty = [v], [0] * m, False
        seen.add(v)
        while stack:
            w = stack.pop()
            if w < s:
                nonempty = True
                row = profiles.rows[w]
                for j in range(m):
                    mass[j] += row.counts[j] * row.multiplicity
            for z in graph[w]:
                if z not in seen:
                    seen.add(z)
                    stack.append(z)
        if nonempty:
            out[tuple(mass)] += 1
    return Profiles.from_histogram(profiles.lengths, out)


def _join(m, block_lists):
    graph = {}
    for blocks in block_lists:
        for block in blocks:
            for a in block:
                graph.setdefault(a, set()).update(block)
    seen, components = set(), []
    for a in sorted(graph):
        if a in seen:
            continue
        reached, frontier = set(), [a]
        while frontier:
            b = frontier.pop()
            if b in reached:
                continue
            reached.add(b)
            frontier.extend(graph[b] - reached)
        seen.update(reached)
        components.append(tuple(sorted(reached)))
    return tuple(sorted(components))


def _program_data(m, records, root):
    if type(m) is not int or m < 0 or not isinstance(records, (list, tuple)) or not records:
        raise ValueError('malformed program')
    lengths, summaries, parsed = [], [], []
    def ref(x, i):
        x = exact_int(x)
        if not 0 <= x < i:
            raise ValueError('invalid grammar reference')
        return x
    for i, node in enumerate(records):
        if not isinstance(node, dict):
            raise ValueError('malformed grammar node')
        op = node.get('op')
        if op == 'cone' and set(node) == {'op', 'atoms'}:
            group = tuple(node['atoms'])
            if any(type(a) is not int or not 0 <= a < m for a in group):
                raise ValueError('invalid atom')
            group = tuple(sorted(set(group)))
            length, summary, item = 1, (group,) if group else (), (op, group)
        elif op == 'concat' and set(node) == {'op', 'left', 'right'}:
            a, b = ref(node['left'], i), ref(node['right'], i)
            length = lengths[a] + lengths[b]
            summary, item = _join(m, (summaries[a], summaries[b])), (op, a, b)
        elif op == 'power' and set(node) == {'op', 'child', 'exponent'}:
            a, p = ref(node['child'], i), exact_int(node['exponent'])
            if p < 0:
                raise ValueError('negative power')
            length, summary, item = lengths[a] * p, summaries[a] if p else (), (op, a, p)
        else:
            raise ValueError('invalid grammar node')
        lengths.append(length)
        summaries.append(summary)
        parsed.append(item)
    root = exact_int(root)
    if not 0 <= root < len(records):
        raise ValueError('invalid grammar root')
    return lengths, summaries, parsed


def checked_prefix_blocks(m, records, root, prefix):
    root = exact_int(root)
    lengths, summaries, parsed = _program_data(m, records, root)
    prefix = exact_int(prefix)
    if not 0 <= prefix <= lengths[root]:
        raise ValueError('invalid prefix')
    # Stack formulation, independently of the producer's single-path walker.
    stack, pieces = [(root, prefix)], []
    while stack:
        node, k = stack.pop()
        if k == 0:
            continue
        if k == lengths[node]:
            pieces.append(summaries[node])
            continue
        item = parsed[node]
        if item[0] == 'concat':
            a, b = item[1:]
            left = min(k, lengths[a])
            if k > left:
                stack.append((b, k - left))
            stack.append((a, left))
        elif item[0] == 'power':
            a = item[1]
            if not lengths[a]:
                raise ValueError('nonempty prefix of empty power')
            quotient, remainder = divmod(k, lengths[a])
            if quotient:
                pieces.append(summaries[a])
            if remainder:
                stack.append((a, remainder))
        else:
            raise ValueError('invalid cone prefix')
    return _join(m, pieces)


def verify_quotient(profiles, cones, claimed):
    try:
        if not isinstance(claimed, Profiles):
            claimed = Profiles.from_dict(claimed)
        return graph_quotient(profiles, cones) == claimed
    except (ValueError, TypeError, KeyError):
        return False


def verify_threshold(profiles, records, root, target, index):
    """Verify a claimed FIRST threshold location with two adjacent prefixes.

    None is the precise claim that the threshold is never attained.
    """
    try:
        target = exact_int(target)
        root = exact_int(root)
        lengths, summaries, _ = _program_data(len(profiles.lengths), records, root)
        if index is None:
            return graph_quotient(profiles, summaries[root]).orbit_count > target
        index = exact_int(index)
        if index == 0:
            return profiles.orbit_count <= target
        if not 1 <= index <= lengths[root]:
            return False
        before = checked_prefix_blocks(len(profiles.lengths), records, root, index - 1)
        after = checked_prefix_blocks(len(profiles.lengths), records, root, index)
        return (graph_quotient(profiles, before).orbit_count > target >=
                graph_quotient(profiles, after).orbit_count)
    except (ValueError, TypeError, KeyError, IndexError):
        return False


def verify_change_points(profiles, records, root, events):
    """Check all reported drops and all omitted plateaux independently.

    Monotonicity of the validated fixed-cone grammar makes equal endpoint
    counts a proof that an omitted interval contains no count-changing step.
    """
    try:
        m = len(profiles.lengths)
        lengths, summaries, nodes = _program_data(m, records, root)
        root = exact_int(root)
        if not 0 <= root < len(nodes) or not isinstance(events, (list, tuple)):
            return False
        total = lengths[root]
        previous_index, previous_count = 0, profiles.orbit_count
        for event in events:
            if not isinstance(event, dict) or set(event) != {'index', 'before', 'after'}:
                return False
            index, before, after = (exact_int(event[k]) for k in ('index', 'before', 'after'))
            if not previous_index < index <= total or not before > after:
                return False
            prior = graph_quotient(profiles, checked_prefix_blocks(m, records, root, index-1))
            later = graph_quotient(profiles, checked_prefix_blocks(m, records, root, index))
            if prior.orbit_count != before or later.orbit_count != after or before != previous_count:
                return False
            previous_index, previous_count = index, after
        final = graph_quotient(profiles, checked_prefix_blocks(m, records, root, total))
        return previous_count == final.orbit_count
    except (ValueError, TypeError, KeyError, IndexError):
        return False
