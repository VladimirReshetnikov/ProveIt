"""Independent exact verifier: no imports from producer or atlas modules.

The verifier independently checks source no-fill predicates. It transports a
saturated total and an owner residue modulo q+1. The residue is read ONLY
when the exact total equals one, so it is not a probabilistic fingerprint.
"""
from collections.abc import Mapping


def verify_certificate(real, n, passive, certificate, *, require_complete=False):
    """Return bool; malformed or unsupported records are rejected.

    real/passive must be supplied independently of certificate generation.
    This proves the matrix query, not source geometry or a knot verdict.
    """
    try:
        return _verify(real, n, passive, certificate, require_complete)
    except (ValueError, TypeError, KeyError, IndexError, OverflowError):
        return False


def _verify(real, n, passive, c, complete):
    if type(n) is not int or n < 0 or type(c) is not dict:
        return False
    if set(c) != {"schema", "n_columns", "n_passive", "pivots", "least_private"}:
        return False
    q, m = len(passive), len(real)
    if c["schema"] != "private-cocore-owner-v1":
        return False
    if type(c['n_columns']) is not int or type(c['n_passive']) is not int:
        return False
    if c['n_columns'] != n or c['n_passive'] != q:
        return False
    for rows in (real, passive):
        for row in rows:
            if not isinstance(row, Mapping):
                return False
            for h, w in row.items():
                if type(h) is not int or not 0 <= h < n:
                    return False
                if type(w) is not int or w < 0:
                    return False
    schedule = c['pivots']
    if type(schedule) is not list or len(schedule) != m:
        return False
    row_time, column_time = [-1] * m, [m] * n
    for t, pair in enumerate(schedule):
        if type(pair) is not list or len(pair) != 2:
            return False
        r, g = pair
        if type(r) is not int or type(g) is not int:
            return False
        if not (0 <= r < m and 0 <= g < n):
            return False
        if row_time[r] != -1 or column_time[g] != m or real[r].get(g) != 1:
            return False
        row_time[r], column_time[g] = t, t
    row_has_future, col_has_future_row = [False] * m, [False] * m
    for r, row in enumerate(real):
        for h, w in row.items():
            if not w:
                continue
            if column_time[h] > row_time[r]:
                row_has_future[row_time[r]] = True
            if column_time[h] < row_time[r]:
                col_has_future_row[column_time[h]] = True
    if any(x and y for x, y in zip(row_has_future, col_has_future_row)):
        return False
    count, residue = [0] * n, [0] * n
    modulus = q + 1
    for i, row in enumerate(passive):
        for h, w in row.items():
            count[h] = min(2, count[h] + min(2, w))
            residue[h] = (residue[h] + (w % modulus) * (i + 1)) % modulus
    for t, (r, g) in enumerate(schedule):
        cg, rg = count[g], residue[g]
        for h, w in real[r].items():
            if column_time[h] > t and w:
                count[h] = min(2, count[h] + cg * min(2, w))
                residue[h] = (residue[h] + rg * (w % modulus)) % modulus
        count[g] = residue[g] = 0
    expected = [-1] * q
    for h in range(n):
        if column_time[h] == m and count[h] == 1:
            i = residue[h] - 1
            if not 0 <= i < q:
                return False
            if expected[i] == -1:
                expected[i] = h
    claimed = c['least_private']
    if type(claimed) is not list or any(type(x) is not int for x in claimed):
        return False
    return claimed == expected and (not complete or all(h >= 0 for h in expected))
