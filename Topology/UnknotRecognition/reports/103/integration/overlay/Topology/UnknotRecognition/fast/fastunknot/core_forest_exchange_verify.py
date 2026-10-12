"""Independent graph replay for restricted dual/occurrence forest certificates.

This verifier does not import the planner, its graph constructor, its exchange
search or its leaf queue. It authenticates a certificate relative to supplied
endpoint occurrences and crossing rows. It does not authenticate the geometric
source of those data and does not return a knot or handlebody verdict.
"""


def _nonnegative_label(value):
    return type(value) is int and value >= 0


def _read_source(three_handles, endpoints, occurrences, check):
    three = list(three_handles)
    if not all(_nonnegative_label(v) for v in three) or len(set(three)) != len(three):
        raise ValueError('invalid three-handles')
    if type(endpoints) is not dict or type(occurrences) is not dict:
        raise ValueError('invalid source maps')
    if set(endpoints) != set(occurrences):
        raise ValueError('source row labels differ')
    edges, rows = {}, {}
    for e, ends in endpoints.items():
        check()
        if not _nonnegative_label(e) or type(ends) not in (list, tuple) or len(ends) > 2:
            raise ValueError('invalid endpoint row')
        if any(not _nonnegative_label(v) or v not in three for v in ends):
            raise ValueError('unknown endpoint')
        edges[e] = tuple(list(ends) + [-1] * (2 - len(ends)))
        raw = occurrences[e]
        if type(raw) is not dict:
            raise ValueError('invalid occurrence row')
        row = {}
        for c, value in raw.items():
            if not _nonnegative_label(c) or not _nonnegative_label(value):
                raise ValueError('invalid occurrence')
            if value:
                row[c] = 1 if value == 1 else 2
        rows[e] = row
    return set(three) | {-1}, edges, rows


def _rank(vertices, edge_pairs, check):
    """Graphic rank by literal component traversal, including isolated vertices."""
    adjacency = {v: [] for v in vertices}
    for a, b in edge_pairs:
        adjacency[a].append(b)
        adjacency[b].append(a)
    seen, components = set(), 0
    for start in sorted(vertices):
        if start in seen:
            continue
        components += 1
        stack = [start]
        seen.add(start)
        while stack:
            check()
            for other in adjacency[stack.pop()]:
                if other not in seen:
                    seen.add(other)
                    stack.append(other)
    return len(vertices) - components


def _label_list(value, allowed):
    return (type(value) is list and all(_nonnegative_label(x) for x in value)
            and len(set(value)) == len(value) and set(value) <= allowed)


def _pairs(value):
    return (type(value) is list and all(type(pair) is list and len(pair) == 2
            and all(_nonnegative_label(x) for x in pair) for pair in value))


def _dual_complete(vertices, edges, rows, forced, certificate, check):
    forest = certificate['dual_forest']
    if not _label_list(forest, set(rows)) or not forced <= set(forest):
        return False
    top = certificate['two_three_cancellations']
    if not _pairs(top):
        return False
    alive, deleted = vertices - {-1}, set()
    for r, v in top:
        check()
        if r not in forest or r in deleted or v not in alive:
            return False
        # Counting occurrences rejects a loop meeting one 3-handle twice.
        if [w for w in edges[r] if w in alive] != [v]:
            return False
        alive.remove(v)
        deleted.add(r)
    return not alive and deleted == set(forest)


def _complete(vertices, edges, rows, forced, certificate, check):
    expected = {'schema', 'kind', 'dual_forest', 'two_three_cancellations',
                'one_two_cancellations'}
    if set(certificate) != expected:
        return False
    if not _dual_complete(vertices, edges, rows, forced, certificate, check):
        return False

    bottom = certificate['one_two_cancellations']
    if not _pairs(bottom):
        return False
    retained = set(rows) - set(certificate['dual_forest'])
    ordered_rows = [r for r, _ in bottom]
    ordered_columns = [c for _, c in bottom]
    if (len(set(ordered_rows)) != len(ordered_rows) or set(ordered_rows) != retained
            or len(set(ordered_columns)) != len(ordered_columns)):
        return False
    row_time = {r: i for i, r in enumerate(ordered_rows)}
    column_time = {c: (i, r) for i, (r, c) in enumerate(bottom)}
    for r, c in bottom:
        if rows[r].get(c, 0) != 1:
            return False
    # Source timestamps check each no-fill condition without repeating a queue.
    for r in retained:
        check()
        for c in rows[r]:
            if c in column_time:
                timestamp, pivot_row = column_time[c]
                if r != pivot_row and row_time[r] >= timestamp:
                    return False
    return True


def _occurrence_graph(rows, selected):
    edge_pairs = []
    for e in selected:
        ends = []
        for c, value in rows[e].items():
            ends.extend([c] * value)
        if len(ends) > 2:
            raise ValueError('long row in occurrence graph')
        edge_pairs.append(tuple(ends + [-1] * (2 - len(ends))))
    return edge_pairs


def verify_forest_exchange(three_handles, endpoints, occurrences, certificate,
                           *, check=lambda: None):
    """Check a full schedule or an obstruction to the stated restricted strategy.

    A true return for a refusal proof establishes only graph-model infeasibility.
    Neither that return nor a complete graph schedule authenticates native
    geometry, marked-curve transport, or any ambient knot interpretation.
    """
    check()
    try:
        vertices, edges, rows = _read_source(three_handles, endpoints, occurrences, check)
        if type(certificate) is not dict or certificate.get('schema') != 'core-forest-exchange-v1':
            return False
        kind = certificate.get('kind')
        forced = {r for r, row in rows.items() if sum(row.values()) > 2}
        if kind == 'complete':
            return _complete(vertices, edges, rows, forced, certificate, check)
        if kind == 'boundary_disconnected':
            if set(certificate) != {'schema', 'kind', 'vertices'}:
                return False
            separated = certificate['vertices']
            if not separated or not _label_list(separated, vertices - {-1}):
                return False
            part = set(separated)
            return all((a in part) == (b in part) for a, b in edges.values())
        if kind == 'forced_long_cycle':
            if set(certificate) != {'schema', 'kind', 'rows', 'rank'}:
                return False
            selected = certificate['rows']
            if not selected or not _label_list(selected, forced):
                return False
            rank = _rank(vertices, [edges[e] for e in selected], check)
            return (_nonnegative_label(certificate['rank'])
                    and certificate['rank'] == rank < len(selected))
        if kind != 'short_row_rank_obstruction':
            return False
        expected = {'schema', 'kind', 'rows', 'ranks', 'deficiency', 'dual_forest',
                    'two_three_cancellations', 'occurrence_forest', 'unassigned_rows'}
        if set(certificate) != expected:
            return False
        selected = certificate['rows']
        if not selected or not _label_list(selected, set(rows) - forced):
            return False
        if _rank(vertices, [edges[e] for e in forced], check) != len(forced):
            return False
        dual_rank = _rank(vertices, [edges[e] for e in forced | set(selected)], check)
        dual_rank -= len(forced)
        columns = {c for row in rows.values() for c in row} | {-1}
        occurrence_rank = _rank(columns, _occurrence_graph(rows, selected), check)
        ranks = certificate['ranks']
        deficiency = certificate['deficiency']
        if not (type(ranks) is list and len(ranks) == 2
                and all(_nonnegative_label(r) for r in ranks)
                and ranks == [dual_rank, occurrence_rank]
                and _nonnegative_label(deficiency) and deficiency > 0
                and len(selected) - sum(ranks) == deficiency):
            return False
        if not _dual_complete(vertices, edges, rows, forced, certificate, check):
            return False
        retained = set(rows) - set(certificate['dual_forest'])
        occurrence_forest = certificate['occurrence_forest']
        unassigned = certificate['unassigned_rows']
        if (not _label_list(occurrence_forest, retained)
                or not _label_list(unassigned, retained)
                or set(occurrence_forest) & set(unassigned)
                or set(occurrence_forest) | set(unassigned) != retained
                or len(unassigned) != deficiency):
            return False
        forest_rank = _rank(columns, _occurrence_graph(rows, occurrence_forest), check)
        residual_rank = _rank(columns, _occurrence_graph(rows, retained), check)
        return (forest_rank == len(occurrence_forest)
                and len(retained) - residual_rank == deficiency)
    except (KeyError, TypeError, ValueError, IndexError):
        return False
