"""Complete full-row decision for the nonnegative positive-pivot calculus.

The data are geometric occurrence COUNTS, not signed exponent sums. This
module proves only a matrix statement. Authentication of a handle structure
and of its allowed cancellations belongs to the enclosing geometry checker.

After normalization, each incidence is visited once on construction and at
most once on deletion. Python dictionaries give expected/amortized map costs;
the deterministic linear incidence bound uses compact, array-indexed labels.
"""
from collections import deque
from collections.abc import Callable


def column_cancellation_plan(counts: dict[int, dict[int, int]], *,
                             check: Callable[[], None] = lambda: None) -> dict:
    """Return a private-column schedule and its canonical stopping residual.

    Values >=2 are saturated. Zero rows are retained. Labels must be
    nonnegative genuine integers (bool is rejected). Input is not modified.
    A nonempty residual excludes *full positive elimination*, not handlebody
    topology and not further partial positive pivots. The schedule format is
    compatible with the native general ('capped') positive-pivot verifier.
    """
    check()
    if type(counts) is not dict:
        raise ValueError('counts must be a dictionary')
    labels, rows, totals, owners = [], [], {}, {}
    input_entries = 0
    for r, values in counts.items():
        check()
        if type(r) is not int or r < 0 or type(values) is not dict:
            raise ValueError('invalid occurrence row')
        index = len(labels) + 1  # zero is reserved for the empty XOR
        labels.append(r)
        row = []
        for c, value in values.items():
            check()
            input_entries += 1
            if type(c) is not int or c < 0 or type(value) is not int or value < 0:
                raise ValueError('invalid occurrence entry')
            if value:
                v = min(2, value)
                row.append((c, v))
                totals[c] = totals.get(c, 0) + v
                owners[c] = owners.get(c, 0) ^ index
        rows.append(row)
    pending = deque(c for c, total in totals.items() if total == 1)
    alive = [True] * len(rows)
    schedule, visits, pops = [], 0, 0
    while pending:
        check()
        c = pending.popleft()
        pops += 1
        if totals[c] != 1:
            continue
        i = owners[c] - 1
        if not (0 <= i < len(rows)) or not alive[i]:
            raise ArithmeticError('private-column owner invariant failed')
        alive[i] = False
        schedule.append([labels[i], c])
        for h, v in rows[i]:
            check()
            visits += 1
            totals[h] -= v
            owners[h] ^= i + 1
            if totals[h] == 1:
                pending.append(h)
    check()
    return dict(cancellations=schedule,
                remaining_rows=[r for r, live in zip(labels, alive) if live],
                stats=dict(input_entries=input_entries,
                           nonzero_entries=sum(map(len, rows)),
                           incidence_deletions=visits, queue_pops=pops,
                           entry_updates=0))
