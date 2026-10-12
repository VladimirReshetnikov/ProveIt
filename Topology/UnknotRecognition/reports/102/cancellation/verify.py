"""Independent certificate checks: imports no scheduling/deferral producer."""
from collections.abc import Callable


class _BadMatrix(ValueError):
    pass


def _matrix(counts, *, check=lambda: None):
    if type(counts) is not dict:
        raise _BadMatrix('invalid matrix')
    result = {}
    for r, row in counts.items():
        check()
        if type(r) is not int or r < 0 or type(row) is not dict:
            raise _BadMatrix('invalid row')
        result[r] = {}
        for c, v in row.items():
            check()
            if type(c) is not int or c < 0 or type(v) is not int or v < 0:
                raise _BadMatrix('invalid entry')
            if v:
                result[r][c] = 1 if v == 1 else 2
    return result


def verify_stopping_set(counts, selected, *, check: Callable[[], None] = lambda: None):
    """Check a nonempty obstruction against ALL original columns."""
    try:
        matrix = _matrix(counts, check=check)
    except _BadMatrix:
        return False
    if type(selected) is not list or not selected:
        return False
    if any(type(r) is not int or r not in matrix for r in selected):
        return False
    if len(set(selected)) != len(selected):
        return False
    sums = {}
    for r in selected:
        check()
        for c, v in matrix[r].items():
            sums[c] = min(2, sums.get(c, 0) + v)
    return all(v != 1 for v in sums.values())

def verify_peeling_certificate(counts, certificate, *, require_complete=False,
                               check: Callable[[], None] = lambda: None):
    """Verify triangular timestamps, partition, and the maximal stopping core.

    Accept only the exact small schema; a successful check authenticates a
    matrix claim, never the source geometry. Callback exceptions propagate.
    """
    try:
        matrix = _matrix(counts, check=check)
    except _BadMatrix:
        return False
    if (type(certificate) is not dict or set(certificate) !=
            {'schema', 'cancellations', 'remaining_rows'}):
        return False
    if certificate['schema'] != 'positive-column-peeling-v1':
        return False
    moves, rest = certificate['cancellations'], certificate['remaining_rows']
    if type(moves) is not list or type(rest) is not list:
        return False
    times, columns = {}, {}
    for t, move in enumerate(moves):
        check()
        if type(move) is not list or len(move) != 2:
            return False
        r, c = move
        if type(r) is not int or type(c) is not int:
            return False
        if r not in matrix or r in times or c in columns:
            return False
        if matrix[r].get(c, 0) != 1:
            return False
        times[r], columns[c] = t, (t, r)
    if (any(type(r) is not int or r not in matrix for r in rest)
            or len(set(rest)) != len(rest) or set(rest) & set(times)
            or set(rest) | set(times) != set(matrix)):
        return False
    if require_complete and rest:
        return False
    infinity = len(moves)
    residual_sums = {}
    for r, row in matrix.items():
        check()
        t = times.get(r, infinity)
        for c, value in row.items():
            check()
            if c in columns:
                pivot_time, pivot_row = columns[c]
                if t > pivot_time or (t == pivot_time and r != pivot_row):
                    return False
            if t == infinity:
                residual_sums[c] = min(2, residual_sums.get(c, 0) + value)
    return not rest or all(v != 1 for v in residual_sums.values())

def replay_positive(counts, moves, *, require_complete=False,
                    check: Callable[[], None] = lambda: None):
    """Independent dense-style positive replay. Return residual, or None.

    Deliberately not optimized: a reference oracle for supplied schedules.
    """
    try:
        matrix = _matrix(counts, check=check)
    except _BadMatrix:
        return None
    if type(moves) is not list:
        return None
    columns = {c for row in matrix.values() for c in row}
    for move in moves:
        check()
        if type(move) is not list or len(move) != 2:
            return None
        r, c = move
        if (type(r) is not int or type(c) is not int or r not in matrix
                or c not in columns or matrix[r].get(c, 0) != 1):
            return None
        donor = matrix.pop(r)
        columns.remove(c)
        for i, row in matrix.items():
            factor = row.get(c, 0)
            for h in columns:
                v = row.get(h, 0) + factor * donor.get(h, 0)
                if v:
                    row[h] = min(2, v)
                else:
                    row.pop(h, None)
            row.pop(c, None)
    if require_complete and matrix:
        return None
    return matrix
