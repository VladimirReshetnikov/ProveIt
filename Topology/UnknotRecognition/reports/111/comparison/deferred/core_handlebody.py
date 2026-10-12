"""Small certificates that an authenticated geometric handle core is a handlebody.

Only a spanning forest and raw geometric 1/2 cancellations are used.  The
attaching curves must come from the source-parallelity handle charts: an
arbitrary group presentation is not an acceptable substitute for this input.
All belt-intersection counts are saturated at two.  No words are expanded,
freely reduced, or replaced by algebraic exponent sums.
"""

# The column queue and its timestamp checker are adapted from report 97;
# report 95 independently derives the same full-row criterion from report 56.
from collections import deque
from heapq import heappop, heappush


def _forest(core, check, forbidden=()):
    count = len(core['handles0'])
    parent = list(range(count))

    def root(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    forbidden = set(forbidden)
    edges = []
    for handle in core['handles1']:
        check()
        if handle['id'] in forbidden:
            continue
        a, b = map(root, handle['ends'])
        if a != b:
            parent[max(a, b)] = min(a, b)
            edges.append(handle['id'])
    roots = [root(a) for a in range(count)]
    return edges, roots


def _occurrences(core, tree, check):
    tree = set(tree)
    rows = {}
    for handle in core['handles2']:
        check()
        row = {}
        for flag in handle['cycle']:
            if flag['dimension'] == 1 and flag['handle'] not in tree:
                h = flag['handle']
                row[h] = min(2, row.get(h, 0) + 1)
        rows[handle['id']] = row
    return rows


def capped_cancellation_plan(counts, *, check=lambda: None):
    """Return a sound raw singleton schedule for nonnegative occurrence rows.

    Kept as the legacy producer and a comparison oracle.  Its minimum-fill
    rule is complete for full row cancellation: whenever completion is
    possible, a zero-fill row or column leaf exists and the minimum score
    selects one.  The source column queue below avoids repeated rescanning.
    Values zero, one and at least two carry all information for admissibility.
    Row and column labels must be nonnegative integers.
    """
    rows = {}
    for r, values in counts.items():
        check()
        if type(r) is not int or r < 0 or type(values) is not dict:
            raise ValueError('invalid occurrence row')
        row = {}
        for c, value in values.items():
            if type(c) is not int or c < 0 or type(value) is not int or value < 0:
                raise ValueError('invalid occurrence entry')
            if value:
                row[c] = min(2, value)
        rows[r] = row
    schedule, updates, scans = [], 0, 0
    while rows:
        check()
        totals = {}
        for row in rows.values():
            for c, value in row.items():
                totals[c] = totals.get(c, 0) + value
                scans += 1
        candidates = []
        for r, row in rows.items():
            size = sum(row.values())
            for c, value in row.items():
                scans += 1
                if value == 1:
                    candidates.append(((size - 1) * (totals[c] - 1), size, r, c))
        if not candidates:
            break
        _, _, r, c = min(candidates)
        donor = rows.pop(r)
        donor.pop(c)
        for row in rows.values():
            check()
            multiplicity = row.pop(c, 0)
            if multiplicity:
                for h, value in donor.items():
                    row[h] = min(2, row.get(h, 0) + multiplicity * value)
                    updates += 1
        schedule.append([r, c])
    return dict(cancellations=schedule, remaining_rows=sorted(rows),
                stats=dict(entry_scans=scans, entry_updates=updates))


def column_cancellation_plan(counts, *, check=lambda: None):
    """Completely decide full raw row cancellation without positive fill.

    A unit column leaf has total live incidence one.  Delete its sole row
    and the column.  Other columns retain their immutable source entries.
    The process succeeds exactly when *some* positive-singleton schedule
    can remove every row, for arbitrary rectangular nonnegative matrices.

    If it stops, the surviving rows form the unique greatest nonempty
    blocked set: every column sum on those rows is zero or at least two.
    This is an obstruction only to the specified raw cancellation model.
    Discovery processes each source incidence a bounded number of times.
    Queue order follows the input dictionaries and needs no label sorting.
    """
    check()
    if type(counts) is not dict:
        raise ValueError('invalid occurrence matrix')
    rows, degree, owner_xor = {}, {}, {}
    incidences = 0
    for r, values in counts.items():
        check()
        if type(r) is not int or r < 0 or type(values) is not dict:
            raise ValueError('invalid occurrence row')
        row = {}
        for c, value in values.items():
            check()
            if type(c) is not int or c < 0 or type(value) is not int or value < 0:
                raise ValueError('invalid occurrence entry')
            if value:
                incidences += 1
                row[c] = min(2, value)
                degree[c] = degree.get(c, 0) + 1
                owner_xor[c] = owner_xor.get(c, 0) ^ r
        rows[r] = row
    queue = deque(c for c in degree
                  if degree[c] == 1 and rows[owner_xor[c]][c] == 1)
    pushes, pops, visits = len(queue), 0, 0
    schedule = []
    while queue:
        check()
        c = queue.popleft()
        pops += 1
        if degree[c] != 1:
            continue
        r = owner_xor[c]
        row = rows.pop(r)
        if row[c] != 1:
            raise ArithmeticError('nonunit entry entered the column-leaf queue')
        schedule.append([r, c])
        for h in row:
            check()
            visits += 1
            degree[h] -= 1
            owner_xor[h] ^= r
            if degree[h] == 1 and rows[owner_xor[h]][h] == 1:
                queue.append(h)
                pushes += 1
    check()
    return dict(cancellations=schedule, remaining_rows=list(rows),
                stats=dict(source_incidences=incidences,
                           incidence_visits=visits, queue_pushes=pushes,
                           queue_pops=pops, entry_updates=0))


def leaf_cancellation_plan(counts, *, check=lambda: None):
    """Peel source rows having one remaining crossing, without fill or words.

    For a square occurrence matrix this is complete for raw singleton
    eliminability: permanent one is equivalent to this leaf ordering.  For
    rectangular matrices a stalled pass is only a conservative failure.
    """
    rows = {r: {c: min(2, v) for c, v in values.items() if v}
            for r, values in counts.items()}
    incident = {}
    for r, row in rows.items():
        for c in row:
            incident.setdefault(c, []).append(r)
    queue = []
    for r, row in rows.items():
        if len(row) == 1 and next(iter(row.values())) == 1:
            heappush(queue, r)
    schedule, visits = [], 0
    while queue:
        check()
        r = heappop(queue)
        if r not in rows:
            continue
        row = rows[r]
        if len(row) != 1 or next(iter(row.values())) != 1:
            continue
        rows.pop(r)
        c = next(iter(row))
        schedule.append([r, c])
        for i in incident[c]:
            check()
            visits += 1
            if i in rows:
                rows[i].pop(c, None)
                if len(rows[i]) == 1 and next(iter(rows[i].values())) == 1:
                    heappush(queue, i)
    return dict(cancellations=schedule, remaining_rows=sorted(rows),
                stats=dict(incidence_visits=visits))


def core_handlebody_certificate(core, *, check=lambda: None,
                               forest_strategy='canonical'):
    """Plan certified cancellations on a source-authenticated geometric core.

    A COMPLETE result gives a handlebody for each core component.  Three-handles
    and stalled raw cancellation produce INCONCLUSIVE, never a negative result.
    Authenticating the source and its handle charts belongs to the enclosing
    normal-cut certificate.  The small certificate is checked independently by
    ``verify_core_handlebody_certificate``.  ``forest_strategy='deferred'``
    peels all source columns before selecting a forest disjoint from its
    pivots.  Closed attaching walks guarantee that such a forest exists.
    This decides success over every primal forest, for a fixed set of rows.
    The legacy canonical strategy remains the default.
    """
    check()
    if forest_strategy not in ('canonical', 'deferred'):
        raise ValueError('unknown core forest strategy')
    result = dict(status='INCONCLUSIVE',
                  trust='geometric core cancellation; requires authenticated handle charts')
    if core['handles3']:
        result['reason'] = 'core_has_three_handles'
        return result
    if forest_strategy == 'deferred':
        counts = _occurrences(core, (), check)
        planned = column_cancellation_plan(counts, check=check)
        method = 'column_leaf'
        if planned['remaining_rows']:
            result.update(reason='all_primal_forests_raw_obstruction',
                          remaining_two_handles=planned['remaining_rows'],
                          stats=planned['stats'])
            return result
        pivots = {c for _, c in planned['cancellations']}
        tree, component = _forest(core, check, forbidden=pivots)
        # Each pivot occurs once on a surviving closed attaching walk, and
        # hence is not a bridge after deletion of the earlier pivots.
        # Reject malformed geometry instead of emitting an invalid forest.
        for handle in core['handles1']:
            check()
            a, b = handle['ends']
            if component[a] != component[b]:
                raise ArithmeticError('deferred pivots disconnected a source component')
    else:
        tree, component = _forest(core, check)
        counts = _occurrences(core, tree, check)
        planned = leaf_cancellation_plan(counts, check=check)
        method = 'leaf'
        if planned['remaining_rows']:
            planned = column_cancellation_plan(counts, check=check)
            method = 'column_leaf'
    result['stats'] = planned['stats']
    if planned['remaining_rows']:
        reason = ('raw_ball_cancellation_obstruction'
                  if len(core['handles1']) - len(tree) == len(core['handles2'])
                  else 'raw_cancellation_stalled')
        result.update(reason=reason,
                      remaining_two_handles=planned['remaining_rows'])
        return result
    survivors = set(range(len(core['handles1']))) - set(tree)
    survivors.difference_update(c for _, c in planned['cancellations'])
    components = []
    for representative in sorted(set(component)):
        check()
        vertices = [i for i, r in enumerate(component) if r == representative]
        loops = [i for i in sorted(survivors)
                 if component[core['handles1'][i]['ends'][0]] == representative]
        components.append(dict(id=representative, zero_handles=vertices,
                               remaining_one_handles=loops, genus=len(loops)))
    schema = ('normal-core-handlebody-v2' if method == 'column_leaf'
              else 'normal-core-handlebody-v1')
    proof = dict(schema=schema, method=method, forest=tree,
                 cancellations=planned['cancellations'], components=components)
    result.update(status='COMPLETE', certificate=proof, components=components)
    check()
    return result
