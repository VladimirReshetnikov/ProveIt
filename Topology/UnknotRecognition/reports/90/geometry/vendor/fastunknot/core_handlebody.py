"""Small certificates that an authenticated geometric handle core is a handlebody.

Only a spanning forest and raw geometric 1/2 cancellations are used.  The
attaching curves must come from the source-parallelity handle charts: an
arbitrary group presentation is not an acceptable substitute for this input.
All belt-intersection counts are saturated at two.  No words are expanded,
freely reduced, or replaced by algebraic exponent sums.
"""

from heapq import heappop, heappush


def _forest(core, check):
    count = len(core['handles0'])
    parent = list(range(count))

    def root(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    edges = []
    for handle in core['handles1']:
        check()
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

    This deterministic greedy producer is deliberately incomplete.  The
    independent verifier accepts any supplied successful schedule.  Values
    zero, one and at least two carry all information needed for admissibility.
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


def core_handlebody_certificate(core, *, check=lambda: None):
    """Plan certified cancellations on a source-authenticated geometric core.

    A COMPLETE result gives a handlebody for each core component.  Three-handles
    and stalled raw cancellation produce INCONCLUSIVE, never a negative result.
    Authenticating the source and its handle charts belongs to the enclosing
    normal-cut certificate.  The small certificate is checked independently by
    ``verify_core_handlebody_certificate``.
    """
    check()
    result = dict(status='INCONCLUSIVE',
                  trust='geometric core cancellation; requires authenticated handle charts')
    if core['handles3']:
        result['reason'] = 'core_has_three_handles'
        return result
    tree, component = _forest(core, check)
    counts = _occurrences(core, tree, check)
    planned = leaf_cancellation_plan(counts, check=check)
    method = 'leaf'
    if planned['remaining_rows']:
        columns = len(core['handles1']) - len(tree)
        if columns == len(core['handles2']):
            result.update(reason='raw_ball_cancellation_obstruction',
                          remaining_two_handles=planned['remaining_rows'],
                          stats=planned['stats'])
            return result
        planned = capped_cancellation_plan(counts, check=check)
        method = 'capped'
    result['stats'] = planned['stats']
    if planned['remaining_rows']:
        result.update(reason='raw_cancellation_stalled',
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
    proof = dict(schema='normal-core-handlebody-v1', method=method, forest=tree,
                 cancellations=planned['cancellations'], components=components)
    result.update(status='COMPLETE', certificate=proof, components=components)
    check()
    return result
