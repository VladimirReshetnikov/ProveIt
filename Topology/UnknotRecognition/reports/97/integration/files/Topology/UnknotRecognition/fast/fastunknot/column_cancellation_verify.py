"""Independent immutable-source checks for raw column cancellation.

These are algebraic checks on authenticated nonnegative occurrence rows.
They do not certify a geometric handle structure or a knot verdict.  This
module imports no producer and never updates an incidence matrix.
"""


def _valid_counts(counts, check):
    if type(counts) is not dict:
        return False
    for r, row in counts.items():
        check()
        if type(r) is not int or r < 0 or type(row) is not dict:
            return False
        for c, value in row.items():
            check()
            if type(c) is not int or c < 0 or type(value) is not int or value < 0:
                return False
    return True


def verify_column_cancellations(counts, cancellations, *, complete=True,
                                check=lambda: None):
    """Check a no-fill prefix, or a complete trace, by source timestamps."""
    check()
    if type(complete) is not bool or not _valid_counts(counts, check):
        return False
    if type(cancellations) is not list:
        return False
    row_time, column_pivot = {}, {}
    for time, move in enumerate(cancellations):
        check()
        if type(move) is not list or len(move) != 2:
            return False
        r, c = move
        if type(r) is not int or type(c) is not int or c < 0:
            return False
        if r not in counts or r in row_time or c in column_pivot:
            return False
        if counts[r].get(c, 0) != 1:
            return False
        row_time[r] = time
        column_pivot[c] = (r, time)
    if complete and len(row_time) != len(counts):
        return False
    infinity = len(cancellations)
    for r, row in counts.items():
        check()
        for c, value in row.items():
            check()
            if not value or c not in column_pivot:
                continue
            pivot_row, time = column_pivot[c]
            if r != pivot_row and row_time.get(r, infinity) >= time:
                return False
    check()
    return True


def verify_raw_cancellation_obstruction(counts, blocked_rows, *, check=lambda: None):
    """Verify a nonempty row set with no unit column sum.

    Such a set rules out every full positive-singleton cancellation of the
    supplied matrix.  It does not rule out other geometric simplifications.
    Any blocked set suffices; a verifier need not trust canonical discovery.
    """
    check()
    if not _valid_counts(counts, check) or type(blocked_rows) is not list:
        return False
    if not blocked_rows or any(type(r) is not int for r in blocked_rows):
        return False
    selected = set(blocked_rows)
    if len(selected) != len(blocked_rows) or not selected <= counts.keys():
        return False
    totals = {}
    for r in blocked_rows:
        check()
        for c, value in counts[r].items():
            check()
            totals[c] = min(2, totals.get(c, 0) + value)
    check()
    return all(value != 1 for value in totals.values())
