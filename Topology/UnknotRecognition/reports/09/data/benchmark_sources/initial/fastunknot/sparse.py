"""Exact sparse finite-field determinants with measured Schur-complement work.

The pivot rule chooses a shortest active row, then a least-populated column
inside it.  Complete pivoting is permitted: two compact permutation arrays
account for the determinant sign.  The input is copied and may be reused. Prime p is a caller precondition;
primality is not tested. Dictionary bounds use the standard lookup-cost model.

With E stored input entries and F = sum((row_degree-1)*(column_degree-1))
over the selected pivots, the arithmetic work is O(n + E + F), plus n
field inversions; queue work is O((n + E + F) log(n+1)).  No favorable
bound on F is assumed.  This is an exact optimization, not an unknot test.
"""
from __future__ import annotations

from heapq import heapify, heappop, heappush


def sparse_determinant(rows, n=None, p=(1 << 61) - 1, *, check=None, stats=None):
    """Return det(rows) modulo the prime p for sparse square row mappings.

    A zero active row certifies singularity.  ``check`` may raise a resource
    exception; it is polled every pivot and periodically inside a large pivot.
    If supplied, ``stats`` is replaced by deterministic operation counters.
    """
    source = list(rows)
    n = len(source) if n is None else n
    if type(n) is not int or n < 0 or len(source) != n:
        raise ValueError("the matrix must have n rows with n nonnegative")
    if type(p) is not int or p < 2:
        raise ValueError("p must be a prime integer")
    a = []
    columns = [set() for _ in range(n)]
    for i, row in enumerate(source):
        clean = {}
        for j, value in row.items():
            if type(j) is not int or not 0 <= j < n:
                raise ValueError("column index outside square matrix")
            v = value % p
            if v:
                clean[j] = v
                columns[j].add(i)
        a.append(clean)
    row_order = list(range(n))
    column_order = list(range(n))
    row_position = list(range(n))
    column_position = list(range(n))
    queue = [(len(row), i) for i, row in enumerate(a)]
    heapify(queue)
    nonzeros = sum(map(len, a))
    work = {"dimension": n, "input_entries": sum(map(len, source)), "initial_nonzeros": nonzeros,
            "peak_nonzeros": nonzeros, "pivots": 0, "schur_updates": 0,
            "fill_created": 0, "row_swaps": 0, "column_swaps": 0,
            "max_pivot_row": 0, "max_pivot_column": 0,
            "queue_rebuilds": 0, "singular": False}
    determinant = 1
    while row_order:
        if check is not None:
            check()
        while queue:
            length, r = heappop(queue)
            if a[r] is not None and length == len(a[r]):
                break
        else:
            raise ArithmeticError("active row lost from pivot queue")
        if length == 0:
            determinant = 0
            work["singular"] = True
            break
        pivot_row = a[r]
        c = min(pivot_row, key=lambda j: (len(columns[j]), j))
        pivot = pivot_row[c]
        width, height = len(pivot_row), len(columns[c])
        work["pivots"] += 1
        work["max_pivot_row"] = max(work["max_pivot_row"], width)
        work["max_pivot_column"] = max(work["max_pivot_column"], height)
        work["schur_updates"] += (width - 1) * (height - 1)
        determinant = determinant * pivot % p

        # Move the chosen row and column to the last active position.  After
        # eliminating their column, expansion there contributes +pivot.
        pos = row_position[r]
        last = row_order[-1]
        if last != r:
            determinant = -determinant
            work["row_swaps"] += 1
            row_order[pos] = last
            row_position[last] = pos
        row_order.pop()
        pos = column_position[c]
        last = column_order[-1]
        if last != c:
            determinant = -determinant
            work["column_swaps"] += 1
            column_order[pos] = last
            column_position[last] = pos
        column_order.pop()

        tail = [(j, v) for j, v in pivot_row.items() if j != c]
        inverse = pow(pivot, -1, p) if tail and height > 1 else 0
        # Stable order is useful for reproducible counters and certificates.
        for count, i in enumerate(sorted(columns[c] - {r})):
            if check is not None and not count & 127:
                check()
            row = a[i]
            value = row.pop(c)
            nonzeros -= 1
            if tail:
                factor = value * inverse % p
                for j, v in tail:
                    old = row.get(j, 0)
                    new = (old - factor * v) % p
                    if new:
                        row[j] = new
                        if not old:
                            columns[j].add(i)
                            nonzeros += 1
                            work["fill_created"] += 1
                    elif old:
                        del row[j]
                        columns[j].remove(i)
                        nonzeros -= 1
            heappush(queue, (len(row), i))
            work["peak_nonzeros"] = max(work["peak_nonzeros"], nonzeros)
        for j in pivot_row:
            columns[j].discard(r)
        columns[c].clear()
        nonzeros -= width
        a[r] = None
        # Bound stale-priority memory by O(n), charging each rebuild to the
        # insertions since the preceding rebuild.
        if len(queue) > max(64, 4 * len(row_order)):
            queue = [(len(a[i]), i) for i in row_order]
            heapify(queue)
            work["queue_rebuilds"] += 1
    if stats is not None:
        stats.clear()
        stats.update(work)
    return determinant % p
