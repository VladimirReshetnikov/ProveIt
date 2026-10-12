"""Independent feasible-plan replay. Does not import the dynamic-programming producer.

A feasible matching proves the achieved reduction, not its optimality.
Optimality requires the DP, exhaustive oracle, or a complete transfer-table proof.
"""
from __future__ import annotations
from collections import deque


def replay(matrix: list[list[int]], weights: list[int], certificate: dict,
           *, columns: int | None = None,
           forbidden_pivots: set[tuple[int, int]] | None = None) -> dict:
    m = len(matrix)
    n = len(matrix[0]) if m else (columns or 0)
    if any(len(row) != n for row in matrix) or len(weights) != m:
        raise ValueError('bad dimensions')
    if any(type(v) is not int or v < 0 for row in matrix for v in row):
        raise ValueError('bad count')
    if any(type(w) is not int or w < 0 for w in weights):
        raise ValueError('bad weight')
    if certificate.get('schema') != 'ordered-pivot-plan-v1':
        raise ValueError('unsupported certificate schema')
    forbidden_pivots = forbidden_pivots or set()
    pivots, used = {}, set()
    for pair in certificate.get('matching', []):
        if not isinstance(pair, (list, tuple)) or len(pair) != 2:
            raise ValueError('malformed pivot')
        i, j = pair
        if type(i) is not int or type(j) is not int or not (0 <= i < m and 0 <= j < n):
            raise ValueError('out-of-range pivot')
        if i in pivots or j in used or matrix[i][j] != 1 or (i, j) in forbidden_pivots:
            raise ValueError('not an allowed unit matching')
        pivots[i] = j
        used.add(j)
    deferred = sorted(set(range(m))-pivots.keys())
    if certificate.get('deferred_rows') != deferred:
        raise ValueError('incorrect deferred row inventory')
    score = sum(weights[i] for i in pivots)
    if certificate.get('retained_weight') != score or certificate.get('deferred_weight') != sum(weights)-score:
        raise ValueError('incorrect objective')
    # Direct triangular dependency graph, independent of bag-order states.
    outgoing = {i: [] for i in pivots}
    indegree = {i: 0 for i in pivots}
    for owner, col in pivots.items():
        for other in pivots:
            if other != owner and matrix[other][col] > 0:
                outgoing[other].append(owner)
                indegree[owner] += 1
    queue = deque(sorted(i for i in pivots if indegree[i] == 0))
    schedule = []
    while queue:
        i = queue.popleft()
        schedule.append([i, pivots[i]])
        for j in outgoing[i]:
            indegree[j] -= 1
            if indegree[j] == 0:
                queue.append(j)
    if len(schedule) != len(pivots):
        raise ValueError('alternating cycle: matching is not privately peelable')
    # Replay on the original active submatrix; deferred rows are passive, not erased.
    active = set(pivots)
    for i, j in schedule:
        if any(matrix[k][j] for k in active if k != i):
            raise ValueError('non-private replay pivot')
        active.remove(i)
    return {'valid': True, 'schedule': schedule, 'deferred_rows': deferred,
            'retained_weight': score, 'deferred_weight': sum(weights)-score,
            'scope': 'abstract positive-occurrence matrix only'}


def transport(matrix: list[list[int]], schedule: list[list[int]]) -> dict:
    """Explicit exact positive updates, for small audits and downstream integration.

    This is not a compressed boundary-word or embedded-band exporter.
    """
    a = {i: {j: x for j, x in enumerate(row) if x} for i, row in enumerate(matrix)}
    removed_columns = set()
    for r, c in schedule:
        if r not in a or c in removed_columns or a[r].get(c) != 1:
            raise ValueError('illegal unit cancellation')
        donor = a.pop(r)
        for row in a.values():
            factor = row.pop(c, 0)
            if factor:
                for j, x in donor.items():
                    if j != c:
                        row[j] = row.get(j, 0) + factor*x
        removed_columns.add(c)
    return {'remaining_rows': sorted(a), 'removed_columns': sorted(removed_columns),
            'rows': {str(i): {str(j): x for j, x in row.items()} for i, row in a.items()}}
