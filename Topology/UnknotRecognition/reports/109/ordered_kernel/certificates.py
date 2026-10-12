"""Independent linear-incidence feasibility replay and passive count transport.

This module does not import the dynamic program or use its boundary orders.
A successful replay proves feasibility and the displayed cost, not optimality.
"""
from collections import deque
from .model import Matrix, Check, noop


def peeling_plan(matrix: Matrix, deferred, *, check: Check = noop):
    active = set(matrix.rows) - set(deferred)
    degree, owner_xor = {}, {}
    for r in active:
        for c in matrix.entries[r]:
            degree[c] = degree.get(c, 0) + 1
            owner_xor[c] = owner_xor.get(c, 0) ^ r
    todo = deque(c for c in degree if degree[c] == 1
                 and matrix.entries[owner_xor[c]][c] == 1)
    moves = []
    while todo:
        check(); c = todo.popleft()
        if degree[c] != 1:
            continue
        r = owner_xor[c]
        if matrix.entries[r][c] != 1:
            continue
        active.remove(r); moves.append([r, c])
        for h in matrix.entries[r]:
            degree[h] -= 1; owner_xor[h] ^= r
            if degree[h] == 1 and matrix.entries[owner_xor[h]][h] == 1:
                todo.append(h)
    return moves, sorted(active)


def verify_plan(counts: dict, plan: dict, weights: dict | None = None,
                *, check: Check = noop) -> bool:
    try:
        matrix = Matrix.parse(counts, weights)
        if not isinstance(plan, dict) or plan.get('schema') != 'ordered-deferral-v1':
            return False
        deferred = plan['deferred_rows']; moves = plan['cancellations']
        if (type(deferred) is not list or len(set(deferred)) != len(deferred)
                or any(type(r) is not int or r not in matrix.entries for r in deferred)
                or type(moves) is not list):
            return False
        active = set(matrix.rows) - set(deferred)
        sums = {}
        for r in active:
            for c, a in matrix.entries[r].items():
                # Saturated entries suffice; totals are not saturated.
                sums[c] = sums.get(c, 0) + min(2, a)
        used = set()
        for pair in moves:
            check()
            if not isinstance(pair, (list, tuple)) or len(pair) != 2:
                return False
            r, c = pair
            if (type(r) is not int or type(c) is not int or r not in active
                    or c in used or matrix.entries[r].get(c) != 1 or sums.get(c) != 1):
                return False
            active.remove(r); used.add(c)
            for h, a in matrix.entries[r].items():
                sums[h] -= min(2, a)
        cost = sum(matrix.weights[r] for r in deferred)
        return not active and type(plan.get('cost')) is int and plan['cost'] == cost
    except (ValueError, KeyError, TypeError):
        return False


def package_plan(matrix: Matrix, deferred, *, method: str, stats: dict,
                 check: Check = noop) -> dict:
    deferred = sorted(deferred)
    moves, residual = peeling_plan(matrix, deferred, check=check)
    if residual:
        raise ArithmeticError('optimization returned an infeasible deferred set')
    result = dict(schema='ordered-deferral-v1', status='OPTIMAL_MATRIX_PLAN',
                  method=method, deferred_rows=deferred, cancellations=moves,
                  cost=sum(matrix.weights[r] for r in deferred), stats=stats,
                  trust='matrix only; source attaching charts are external')
    if not verify_plan(matrix.entries, result, matrix.weights, check=check):
        raise ArithmeticError('independent feasibility replay failed')
    return result


def transport_counts(counts: dict, plan: dict, *, saturated: bool = False,
                     weights: dict | None = None, check: Check = noop) -> dict:
    """Exact passive numerical transport; not a cyclic-word/geometric exporter.

    Finite positive path-sum formula is attributed to the predecessor report.
    """
    if not verify_plan(counts, plan, weights, check=check):
        raise ValueError('invalid matrix plan')
    passive = {r: {c: (min(2, a) if saturated else a) for c, a in counts[r].items() if a}
               for r in plan['deferred_rows']}
    for r, c in plan['cancellations']:
        check()
        for row in passive.values():
            f = row.pop(c, 0)
            if f:
                for h, a in counts[r].items():
                    if h != c and a:
                        x = row.get(h, 0) + f * (min(2, a) if saturated else a)
                        row[h] = min(2, x) if saturated else x
    return passive


def verify_weighted_stopping_optimality(counts: dict, plan: dict, parts,
                                       weights: dict | None = None, *, check: Check = noop) -> bool:
    """Optimality from a feasible plan and disjoint weighted stopping sets.

    Independent of both the DP and SCC discovery. A tight packing need not
    exist for a general matrix; failure here does not refute optimality.
    """
    try:
        if not verify_plan(counts, plan, weights, check=check) or type(parts) is not list:
            return False
        matrix=Matrix.parse(counts,weights); seen=set(); lower=0
        for part in parts:
            check()
            if (type(part) is not list or not part or len(set(part))!=len(part)
                    or any(type(r) is not int or r not in matrix.entries for r in part)
                    or seen.intersection(part)):
                return False
            seen.update(part); sums={}
            for r in part:
                for c,a in matrix.entries[r].items():
                    check();sums[c]=min(2,sums.get(c,0)+min(2,a))
            if 1 in sums.values():
                return False
            lower+=min(matrix.weights[r] for r in part)
        return lower==plan['cost']
    except (ValueError,TypeError,KeyError):
        return False
