"""Complete full-row positive cancellation by immutable column peeling.

This module decides one precisely delimited incidence problem.  A permitted
positive pivot has entry one, deletes its row and column, and updates surviving
entries by A[i,h] + A[i,c] * A[r,h].  The question is whether every source row
can be removed.  No free reduction or signed algebraic cancellation is allowed.

The rectangular criterion is the transpose/empty-seed consequence of the
source-closure theorem in ProveIt report 56.  It is not a general handlebody
recognizer: a geometric application must authenticate the incidence matrix.
"""

from collections import deque


SCHEMA = 'full-row-column-peeling-v1'


def column_peeling_plan(counts, *, check=lambda: None):
    """Return a complete decision and a sparse replay certificate.

    ``counts`` maps nonnegative integer row IDs to dictionaries of nonnegative
    integer column IDs and nonnegative integer occurrence counts.  Boolean
    labels/counts are rejected.  Rows with no positive entries are retained.
    Large counts are capped at two because only geometric multiplicities zero,
    one and at least two matter to the singleton predicate.

    A row is deleted when some column has exactly one occurrence among all
    currently live rows.  This pivot adds no surviving entries.  Queuing each
    column when its total first becomes one makes incidence processing linear.
    Pivot order depends on source dictionary order; the residual row set is
    independent of that order and of every legal column-peeling choice.

    ``OBSTRUCTED`` means that no positive-pivot sequence removes all rows.  It
    does not mean that no individual pivot is available, that the output is a
    maximum partial cancellation, or that a topological object is nontrivial.
    """
    check()
    if type(counts) is not dict:
        raise ValueError('occurrence counts must be a dictionary')
    row_ids = []
    source_rows = []
    totals = {}
    row_xors = {}
    source_entries = 0
    nonzero_entries = 0
    for r, values in counts.items():
        check()
        if type(r) is not int or r < 0 or type(values) is not dict:
            raise ValueError('invalid occurrence row')
        index = len(row_ids)
        row_ids.append(r)
        row = {}
        for c, value in values.items():
            check()
            source_entries += 1
            if type(c) is not int or c < 0 or type(value) is not int or value < 0:
                raise ValueError('invalid occurrence entry')
            if value:
                value = min(2, value)
                row[c] = value
                totals[c] = totals.get(c, 0) + value
                row_xors[c] = row_xors.get(c, 0) ^ index
                nonzero_entries += 1
        source_rows.append(row)

    queue = deque(c for c, total in totals.items() if total == 1)
    queue_pushes = len(queue)
    queue_pops = 0
    visits = 0
    live = [True] * len(row_ids)
    eliminations = []
    while queue:
        check()
        c = queue.popleft()
        queue_pops += 1
        if totals[c] != 1:
            continue
        index = row_xors[c]
        # A total of one identifies exactly one live source occurrence.  The
        # xor is therefore its dense row index, including the valid index 0.
        if not live[index] or source_rows[index].get(c, 0) != 1:
            raise AssertionError('column counter invariant failed')
        live[index] = False
        eliminations.append([row_ids[index], c])
        for h, value in source_rows[index].items():
            check()
            visits += 1
            totals[h] -= value
            row_xors[h] ^= index
            if totals[h] == 1:
                queue.append(h)
                queue_pushes += 1

    remaining = sorted(row_ids[i] for i, active in enumerate(live) if active)
    certificate = dict(schema=SCHEMA, eliminations=eliminations,
                       residual_rows=remaining)
    check()
    return dict(status='OBSTRUCTED' if remaining else 'COMPLETE',
                cancellations=eliminations, remaining_rows=remaining,
                certificate=certificate,
                stats=dict(source_rows=len(row_ids),
                           active_source_columns=len(totals),
                           source_entries=source_entries,
                           nonzero_entries=nonzero_entries,
                           removal_incidence_visits=visits,
                           queue_pushes=queue_pushes,
                           queue_pops=queue_pops,
                           entry_updates=0))
