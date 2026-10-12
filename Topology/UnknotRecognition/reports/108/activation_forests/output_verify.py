"""Independent replay for the factorial-free output-assignment strategy.

Only independently implemented verifier primitives are reused.  This file
does not import either producer, optimizer, SCC compiler, or closure queue.
"""

from itertools import product

from .model import parse_problem, integer
from .verify import (_positive, _complete_negative, _source_analysis, _rado,
                     _partition_count, _partition_encoding)


def _assignment(data, analysis, columns, outputs):
    seeds, reach, ancestors, sources, exceptional = analysis
    mandatory = [group for group in sources if group.isdisjoint(outputs)]
    starts = set(seeds)
    for group in mandatory:
        starts.update(group)
    guaranteed = set()
    for row in starts:
        guaranteed.update(reach[row])
    prerequisites = sorted({row for column, target in zip(columns, outputs)
                             for row, _ in exceptional[column]
                             if row != target and row not in guaranteed})
    eligible = {row for row, edge in enumerate(data.edges)
                if edge is not None and edge[0] != edge[1]}
    demands = [ancestors[row] & eligible for row in prerequisites]
    return mandatory, starts, prerequisites, demands


def _closure(starts, analysis, columns, outputs):
    _, reach, _, _, exceptional = analysis
    active = set()
    for row in starts:
        active.update(reach[row])
    while True:
        previous = len(active)
        for column, target in zip(columns, outputs):
            required = {row for row, _ in exceptional[column] if row != target}
            if required <= active:
                active.update(reach[target])
        if len(active) == previous:
            return active


def _negative(data, certificate):
    if (type(certificate) is not dict
            or certificate.get('schema') != 'activation-output-no-v1'
            or certificate.get('input_sha256') != data.digest):
        return False
    if certificate.get('kind') in ('disconnected', 'immutable_stopping'):
        converted = dict(certificate, schema='activation-forest-no-v1')
        return _complete_negative(data, converted)
    if set(certificate) != {'schema', 'input_sha256', 'kind', 'rank_layer', 'assignments'} \
            or certificate['kind'] != 'exhaustive_assignments':
        return False
    rank_layer = certificate['rank_layer']
    if type(rank_layer) is not bool or (rank_layer and not data.raw_parity):
        return False
    records = certificate['assignments']
    if type(records) is not list:
        return False
    analysis = _source_analysis(data)
    exceptional = analysis[-1]
    columns = tuple(exceptional)
    choices = [tuple(row for row, count in exceptional[column] if count == 1)
               for column in columns]
    iterator = iter(records)
    for outputs in product(*choices):
        record = next(iterator, None)
        if (type(record) is not dict or record.get('outputs') != list(outputs)
                or not all(integer(row) for row in record['outputs'])):
            return False
        mandatory, starts, prerequisites, demands = _assignment(data, analysis, columns, outputs)
        q = len(prerequisites)
        kind = record.get('kind')
        if kind == 'rank_layer_impossible':
            if (set(record) != {'outputs', 'kind'} or not rank_layer
                    or not (len(mandatory) > data.vertices - 1
                            or len(mandatory) + q < data.vertices - 1)):
                return False
            continue
        if kind == 'mandatory_rank':
            if set(record) != {'outputs', 'kind', 'groups', 'rank'} \
                    or not _rado(data, mandatory, record):
                return False
            continue
        if kind != 'partitions' or set(record) != {'outputs', 'kind', 'failures'} \
                or type(record['failures']) is not list:
            return False
        required_blocks = data.vertices - len(mandatory) if rank_layer else None
        failures = record['failures']
        if len(failures) != _partition_count(q + 1, required_blocks):
            return False
        seen = set()
        for proof in failures:
            if type(proof) is not dict:
                return False
            partition = proof.get('partition')
            if (not _partition_encoding(partition, q + 1, required_blocks)
                    or tuple(partition) in seen):
                return False
            seen.add(tuple(partition))
            if proof.get('kind') == 'nonclosure':
                if set(proof) != {'partition', 'kind', 'unreached'}:
                    return False
                row = proof['unreached']
                if not integer(row) or not 0 <= row < len(data.rows):
                    return False
                activated = starts | {row for row, block in
                                       zip(prerequisites, partition[1:]) if block != 0}
                closure = _closure(activated, analysis, columns, outputs)
                if row in closure:
                    return False
            elif proof.get('kind') == 'rank':
                if set(proof) != {'partition', 'kind', 'groups', 'rank'}:
                    return False
                groups = [set(group) for group in mandatory]
                for block in range(1, max(partition) + 1):
                    members = [demands[i] for i, value in enumerate(partition[1:])
                               if value == block]
                    group = set(members[0])
                    for member in members[1:]:
                        group.intersection_update(member)
                    groups.append(group)
                if not _rado(data, groups, proof):
                    return False
            else:
                return False
    return next(iterator, None) is None


def verify_output(problem, result):
    """Independently verify complete output-assignment results."""
    try:
        data = parse_problem(problem)
        if type(result) is not dict or type(result.get('certificate')) is not dict:
            return False
        if result.get('status') == 'SUCCESS':
            return _positive(data, result['certificate'])
        if result.get('status') == 'NO_FOREST':
            return _negative(data, result['certificate'])
        return False
    except (ValueError, TypeError, KeyError, IndexError, AssertionError):
        return False
