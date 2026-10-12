"""Independent immutable verification of column-peeling certificates.

This checker imports no producer function and does not maintain its counters,
xors, queue, or mutable matrix.  Deletion timestamps verify every proposed
column leaf in one source scan.  A second assertion in the same scan verifies
that the residual rows form a stopping set.
"""


def verify_column_peeling_certificate(counts, certificate, *, check=lambda: None):
    """Verify a complete peeling trace and its canonical residual set.

    Return ``False`` for malformed or false certificates.  Caller callback
    exceptions propagate.  A nonempty verified residual proves impossibility
    of cancelling every row by the positive-pivot model, conditional on the
    supplied occurrence matrix being the intended authenticated source.
    """
    check()
    if type(counts) is not dict or type(certificate) is not dict:
        return False
    if set(certificate) != {'schema', 'eliminations', 'residual_rows'}:
        return False
    if certificate['schema'] != 'full-row-column-peeling-v1':
        return False
    moves = certificate['eliminations']
    residual = certificate['residual_rows']
    if type(moves) is not list or type(residual) is not list:
        return False
    if any(type(r) is not int or r < 0 for r in counts):
        return False
    if any(type(r) is not int or r < 0 for r in residual):
        return False
    if residual != sorted(set(residual)):
        return False

    removed_at = {}
    pivot_of = {}
    for time, move in enumerate(moves):
        check()
        if type(move) is not list or len(move) != 2:
            return False
        r, c = move
        if type(r) is not int or type(c) is not int or r < 0 or c < 0:
            return False
        if r not in counts or r in removed_at or c in pivot_of:
            return False
        removed_at[r] = time
        pivot_of[c] = (r, time)
    if set(residual) != set(counts) - set(removed_at):
        return False

    witnessed = set()
    residual_totals = {}
    for r, row in counts.items():
        check()
        if type(row) is not dict:
            return False
        for c, value in row.items():
            check()
            if type(c) is not int or c < 0 or type(value) is not int or value < 0:
                return False
            if not value:
                continue
            if c in pivot_of:
                donor, time = pivot_of[c]
                if r == donor:
                    if value != 1:
                        return False
                    witnessed.add(c)
                elif r not in removed_at or removed_at[r] >= time:
                    return False
            if r not in removed_at:
                residual_totals[c] = min(2, residual_totals.get(c, 0) + value)
    if witnessed != set(pivot_of):
        return False
    if any(total == 1 for total in residual_totals.values()):
        return False
    check()
    return True


def verify_column_obstruction(counts, residual_rows, *, check=lambda: None):
    """Check a nonempty stopping subset without claiming it is maximal.

    This smaller certificate suffices for a negative answer to *full-row raw
    cancellation*.  It is intentionally not a negative topological verdict.
    """
    check()
    if type(counts) is not dict or type(residual_rows) is not list:
        return False
    if not residual_rows or any(type(r) is not int or r < 0 for r in residual_rows):
        return False
    if len(set(residual_rows)) != len(residual_rows):
        return False
    selected = set(residual_rows)
    if not selected <= set(counts):
        return False
    totals = {}
    for r, row in counts.items():
        check()
        if type(r) is not int or r < 0 or type(row) is not dict:
            return False
        for c, value in row.items():
            check()
            if type(c) is not int or c < 0 or type(value) is not int or value < 0:
                return False
            if r in selected and value:
                totals[c] = min(2, totals.get(c, 0) + value)
    check()
    return not any(total == 1 for total in totals.values())
