"""Independent positive and complete-negative certificate replay.

This file imports no producer, peeling queue, SCC implementation, matroid
optimizer, scenario compiler, or partition generator.  It shares only input
validation and canonical input hashing with the producer.
"""

from collections import Counter, defaultdict
from itertools import permutations, product

from .model import parse_problem, integer


def _labels(data, rows):
    """Independent explicit-component graphic rank, including parallel clones."""
    component, rank = {}, 0
    for row in rows:
        edge = data.edges[row]
        if edge is None:
            continue
        a, b = edge
        left, right = component.setdefault(a, a), component.setdefault(b, b)
        if left != right:
            component = {v: left if c == right else c for v, c in component.items()}
            rank += 1
    return rank


def _indices(value, bound):
    return (type(value) is list and len(set(value)) == len(value)
            and all(integer(x) and 0 <= x < bound for x in value))


def _positive(data, certificate):
    if (type(certificate) is not dict or set(certificate) !=
            {'schema', 'input_sha256', 'tree', 'peeling'}):
        return False
    if (certificate['schema'] != 'activation-forest-success-v1'
            or certificate['input_sha256'] != data.digest):
        return False
    tree, peeling = certificate['tree'], certificate['peeling']
    if not _indices(tree, len(data.rows)) or len(tree) != data.vertices - 1:
        return False
    if _labels(data, tree) != len(tree):
        return False
    if type(peeling) is not list:
        return False
    live = set(range(len(data.rows))) - set(tree)
    rows = [dict(row) for row in data.rows]
    counts = Counter()
    for r in live:
        counts.update(rows[r])
    for step in peeling:
        if (type(step) is not list or len(step) != 2
                or not all(integer(x) for x in step)):
            return False
        row, column = step
        if row not in live or rows[row].get(column) != 1 or counts[column] != 1:
            return False
        live.remove(row)
        counts.subtract(rows[row])
    return not live


def verify_success(problem, certificate):
    """Return True exactly when a supplied tree and complete peel replay."""
    try:
        if type(certificate) is dict and 'certificate' in certificate:
            certificate = certificate['certificate']
        return _positive(parse_problem(problem), certificate)
    except (ValueError, TypeError, KeyError, IndexError, AssertionError):
        return False


def _closure(starts, adjacency):
    result = set(starts)
    frontier = list(starts)
    while frontier:
        u = frontier.pop()
        fresh = set(adjacency[u]) - result
        result.update(fresh)
        frontier.extend(fresh)
    return result


def _source_analysis(data):
    # Repeated whole-column scans are intentionally independent of the
    # producer's queue.  Simultaneous removal of all current leaves is exact.
    live = set(range(len(data.rows)))
    while live:
        counts, owners = Counter(), {}
        for row in live:
            for col, value in data.rows[row]:
                counts[col] += value
                owners[col] = row
        removable = {owners[c] for c, a in counts.items() if a == 1}
        if not removable:
            break
        live.difference_update(removable)
    seeds = set(range(len(data.rows))) - live
    occupants = defaultdict(list)
    for row in sorted(live):
        for col, value in data.rows[row]:
            occupants[col].append((row, value))
    outgoing = [set() for _ in data.rows]
    exceptional = {}
    for col, values in sorted(occupants.items()):
        if not any(a == 1 for _, a in values):
            continue
        if len(values) > 2:
            exceptional[col] = values
        elif len(values) == 1:
            seeds.add(values[0][0])
        else:
            (u, a), (v, b) = values
            if a == 1:
                outgoing[v].add(u)
            if b == 1:
                outgoing[u].add(v)
    reach = [_closure([row], outgoing) for row in range(len(data.rows))]
    ancestors = [{row for row in range(len(data.rows)) if target in reach[row]}
                 for target in range(len(data.rows))]
    unseen = set(range(len(data.rows)))
    components = []
    while unseen:
        first = min(unseen)
        group = {row for row in unseen if row in reach[first] and first in reach[row]}
        unseen.difference_update(group)
        components.append(group)
    sources = [group for group in components
               if seeds.isdisjoint(group)
               and all(ancestors[row] <= group for row in group)]
    return seeds, reach, ancestors, sources, exceptional


def _scenario_demands(data, analysis, order, outputs):
    seeds, reach, ancestors, sources, exceptional = analysis
    mandatory = [group for group in sources if group.isdisjoint(outputs)]
    initially = set(seeds)
    for group in mandatory:
        initially.update(group)
    guaranteed = set()
    for row in initially:
        guaranteed.update(reach[row])
    eligible = {row for row, edge in enumerate(data.edges)
                if edge is not None and edge[0] != edge[1]}
    demands = []
    for col, target in zip(order, outputs):
        for row, _ in exceptional[col]:
            if row != target and row not in guaranteed:
                demands.append(ancestors[row] & eligible)
        guaranteed.update(reach[target])
    return mandatory, demands


def _rado(data, groups, proof):
    selected, asserted = proof.get('groups'), proof.get('rank')
    if (not _indices(selected, len(groups)) or not selected
            or not integer(asserted) or asserted < 0):
        return False
    union = set()
    for index in selected:
        union.update(groups[index])
    actual = _labels(data, sorted(union))
    return actual == asserted and actual < len(selected)


def _partition_count(size, blocks):
    # Stirling recurrence independently counts all admissible encodings.
    # The checker validates the supplied encodings, rejects duplicates, and
    # requires this exact count, instead of regenerating producer partitions.
    row = [1]
    for n in range(1, size + 1):
        row = [0] + [(row[k - 1] if k - 1 < len(row) else 0)
                     + (k * row[k] if k < len(row) else 0)
                     for k in range(1, n + 1)]
    return sum(row) if blocks is None else (row[blocks] if 0 <= blocks < len(row) else 0)


def _partition_encoding(value, size, blocks):
    if type(value) is not list or len(value) != size:
        return False
    largest = -1
    for color in value:
        if not integer(color) or color < 0 or color > largest + 1:
            return False
        largest = max(largest, color)
    return blocks is None or largest + 1 == blocks


def _complete_negative(data, certificate):
    if (certificate.get('schema') != 'activation-forest-no-v1'
            or certificate.get('input_sha256') != data.digest):
        return False
    kind = certificate.get('kind')
    if kind == 'disconnected':
        if set(certificate) != {'schema', 'input_sha256', 'kind', 'vertices'}:
            return False
        vertices = certificate['vertices']
        if not _indices(vertices, data.vertices) or not vertices or 0 in vertices:
            return False
        selected = set(vertices)
        return all(e is None or ((e[0] in selected) == (e[1] in selected))
                   for e in data.edges)
    if kind == 'immutable_stopping':
        if set(certificate) != {'schema', 'input_sha256', 'kind', 'rows'}:
            return False
        rows = certificate['rows']
        if not _indices(rows, len(data.rows)) or not rows:
            return False
        counts = Counter()
        for row in rows:
            edge = data.edges[row]
            if edge is not None and edge[0] != edge[1]:
                return False
            counts.update(dict(data.rows[row]))
        return all(value != 1 for value in counts.values())
    if kind != 'exhaustive_scenarios' or set(certificate) != {
            'schema', 'input_sha256', 'kind', 'rank_layer', 'branches'}:
        return False
    rank_layer = certificate['rank_layer']
    if type(rank_layer) is not bool or (rank_layer and not data.raw_parity):
        return False
    branches = certificate['branches']
    if type(branches) is not list:
        return False
    analysis = _source_analysis(data)
    exceptional = analysis[-1]
    iterator = iter(branches)
    for order in permutations(tuple(exceptional)):
        choices = [tuple(row for row, count in exceptional[col] if count == 1)
                   for col in order]
        for outputs in product(*choices):
            branch = next(iterator, None)
            if type(branch) is not dict or branch.get('order') != list(order) \
                    or branch.get('outputs') != list(outputs):
                return False
            mandatory, demands = _scenario_demands(data, analysis, order, outputs)
            subtype = branch.get('kind')
            if subtype == 'rank_layer_impossible':
                if (set(branch) != {'order', 'outputs', 'kind'} or not rank_layer
                        or not (len(mandatory) > data.vertices - 1
                                or len(mandatory) + len(demands) < data.vertices - 1)):
                    return False
            elif subtype == 'mandatory_rank':
                if set(branch) != {'order', 'outputs', 'kind', 'groups', 'rank'} \
                        or not _rado(data, mandatory, branch):
                    return False
            elif subtype == 'empty_demand':
                index = branch.get('demand')
                if (set(branch) != {'order', 'outputs', 'kind', 'demand'}
                        or not integer(index) or not 0 <= index < len(demands)
                        or demands[index]):
                    return False
            elif subtype == 'partitions':
                if set(branch) != {'order', 'outputs', 'kind', 'failures'} \
                        or type(branch['failures']) is not list:
                    return False
                required_blocks = data.vertices - 1 - len(mandatory) if rank_layer else None
                if len(branch['failures']) != _partition_count(len(demands), required_blocks):
                    return False
                seen = set()
                for proof in branch['failures']:
                    if (type(proof) is not dict
                            or set(proof) != {'partition', 'groups', 'rank'}):
                        return False
                    partition = proof['partition']
                    if (not _partition_encoding(partition, len(demands), required_blocks)
                            or tuple(partition) in seen):
                        return False
                    seen.add(tuple(partition))
                    groups = [set(group) for group in mandatory]
                    for color in range(max(partition, default=-1) + 1):
                        members = [demands[i] for i, label in enumerate(partition)
                                   if label == color]
                        group = set(members[0])
                        for member in members[1:]:
                            group.intersection_update(member)
                        groups.append(group)
                    if not _rado(data, groups, proof):
                        return False
            else:
                return False
    return next(iterator, None) is None


def verify_result(problem, result):
    """Verify a complete positive/negative result; inconclusive is not proof."""
    try:
        data = parse_problem(problem)
        if type(result) is not dict or type(result.get('certificate')) is not dict:
            return False
        if result.get('status') == 'SUCCESS':
            return _positive(data, result['certificate'])
        if result.get('status') == 'NO_FOREST':
            return _complete_negative(data, result['certificate'])
        return False
    except (ValueError, TypeError, KeyError, IndexError, AssertionError):
        return False
