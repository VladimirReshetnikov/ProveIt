"""Exact small-deferral search; deferred rows remain actual two-handles."""
from itertools import combinations
from .peeling import column_cancellation_plan


def deferred_plan(counts, k, *, check=lambda: None):
    """Find a schedule leaving <=k rows, or certify absence within that budget.

    Complete enumeration, not a universal quasi-polynomial theorem. A negative
    output's exhaustive search is not packaged as a succinct proof. This
    routine checks budgets in increasing order, so a FOUND result is optimal.
    """
    if type(k) is not int or k < 0:
        raise ValueError('k must be a nonnegative integer')
    # Authenticate the entire input even if some rows will be deferred.
    column_cancellation_plan(counts, check=check)
    labels = list(counts)
    attempts = 0
    for size in range(min(k, len(labels)) + 1):
        for choice in combinations(labels, size):
            check()
            omitted = set(choice)
            active = {r: row for r, row in counts.items() if r not in omitted}
            plan = column_cancellation_plan(active, check=check)
            attempts += 1
            if not plan['remaining_rows']:
                residual = replay_with_passive(counts, list(choice),
                                               plan['cancellations'], check=check)
                return dict(status='FOUND', minimum_deferrals=size, deferred_rows=list(choice),
                            cancellations=plan['cancellations'], residual=residual,
                            subsets_checked=attempts)
    return dict(status='NO_PLAN_WITHIN_BUDGET', budget=k, subsets_checked=attempts)


def replay_with_passive(counts, deferred, moves, *, check=lambda: None):
    """Saturate updates only on the named passive rows, never delete them.

    A private-column schedule on the active submatrix is required. Independent
    replay_positive is the reference checker for the result. Invalid schedules
    raise ValueError. Work: O(input size + k times active incidences), plus maps.
    """
    column_cancellation_plan(counts, check=check)  # strict input validation
    if (type(deferred) is not list or
            any(type(r) is not int or r not in counts for r in deferred) or
            len(set(deferred)) != len(deferred)):
        raise ValueError('invalid deferred rows')
    from .verify import verify_peeling_certificate
    deferred_set = set(deferred)
    active = {r: row for r, row in counts.items() if r not in deferred_set}
    cert = dict(schema='positive-column-peeling-v1', cancellations=moves,
                remaining_rows=[])
    if not verify_peeling_certificate(active, cert, require_complete=True, check=check):
        raise ValueError('not a full private-column schedule on active rows')
    passive = {r: {c: min(2, v) for c, v in counts[r].items() if v} for r in deferred}
    for r, c in moves:
        check()
        donor = counts[r]
        for row in passive.values():
            factor = row.pop(c, 0)
            if factor:
                for h, v in donor.items():
                    if h != c and v:
                        row[h] = min(2, row.get(h, 0) + factor * min(2, v))
    return passive


def transport_exact_counts(counts, deferred, moves, *, check=lambda: None):
    """Exact nonnegative passive counts without expanding attaching words.

    The active submatrix must admit the supplied private-column schedule.
    For u active rows, maximum input entry bit length B and n columns, output
    bit lengths are O(input passive bit length + u*(B+log(n+1))). This remains
    only an occurrence-count operation, not a boundary-word/pattern exporter.
    """
    column_cancellation_plan(counts, check=check)
    if (type(deferred) is not list or
            any(type(r) is not int or r not in counts for r in deferred) or
            len(set(deferred)) != len(deferred)):
        raise ValueError('invalid deferred rows')
    from .verify import verify_peeling_certificate
    deferred_set = set(deferred)
    active = {r: row for r, row in counts.items() if r not in deferred_set}
    cert = dict(schema='positive-column-peeling-v1', cancellations=moves,
                remaining_rows=[])
    if not verify_peeling_certificate(active, cert, require_complete=True, check=check):
        raise ValueError('not a full private-column schedule on active rows')
    passive = {r: {c: v for c, v in counts[r].items() if v} for r in deferred}
    for r, c in moves:
        check()
        for row in passive.values():
            check()
            factor = row.pop(c, 0)
            if factor:
                for h, v in counts[r].items():
                    if h != c and v:
                        row[h] = row.get(h, 0) + factor*v
    return passive
