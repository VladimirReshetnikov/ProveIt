"""Small independent exponential oracles; never used by the optimizer."""
from functools import lru_cache
from itertools import combinations


def private_value(a, weights=None, forbidden=frozenset()):
    m, n = len(a), len(a[0]) if a else 0
    weights = [1]*m if weights is None else weights
    @lru_cache(None)
    def solve(mask):
        best = 0
        for i in range(m):
            if not mask >> i & 1:
                continue
            for j in range(n):
                if a[i][j] == 1 and (i, j) not in forbidden and not any(
                    k != i and mask >> k & 1 and a[k][j] for k in range(m)):
                    best = max(best, weights[i]+solve(mask ^ (1 << i)))
        return best
    # Removing a row from the active set means deferral; we count no reward for it.
    return max(solve(mask) for mask in range(1 << m))


def subset_value(a, weights=None):
    """Exhaust all deferred sets, testing each by a direct private-column queue."""
    m, n = len(a), len(a[0]) if a else 0
    weights = [1]*m if weights is None else weights
    best = 0
    for mask in range(1 << m):
        active = {i for i in range(m) if mask >> i & 1}
        todo = set(active)
        while todo:
            hit = next((i for j in range(n) for i in todo
                        if a[i][j] == 1 and sum(a[k][j] for k in todo) == 1), None)
            if hit is None:
                break
            todo.remove(hit)
        if not todo:
            best = max(best, sum(weights[i] for i in active))
    return best


def positive_value(a, weights=None):
    """Search every legal positive unit pivot, including fill-producing pivots."""
    weights = tuple([1]*len(a) if weights is None else weights)
    @lru_cache(None)
    def solve(rows, ids):
        best = 0
        for i, row in enumerate(rows):
            for j, x in enumerate(row):
                if x == 1:
                    reduced = tuple(tuple(rows[k][ell] + rows[k][j]*row[ell]
                                          for ell in range(len(row)) if ell != j)
                                    for k in range(len(rows)) if k != i)
                    nxt = ids[:i]+ids[i+1:]
                    best = max(best, weights[ids[i]]+solve(reduced, nxt))
        return best
    return solve(tuple(map(tuple, a)), tuple(range(len(a))))


def alternating_value(a, weights=None):
    """Enumerate matchings; test uniqueness by enumerating alternate bijections."""
    from itertools import permutations
    m, n = len(a), len(a[0]) if a else 0
    weights = [1]*m if weights is None else weights
    best = 0
    def visit(i, matching, used):
        nonlocal best
        if i == m:
            rr = tuple(matching)
            cc = tuple(matching.values())
            count = 0
            for p in permutations(cc):
                if all(a[r][c] > 0 for r, c in zip(rr, p)):
                    count += 1
                    if count > 1:
                        return
            best = max(best, sum(weights[r] for r in rr))
            return
        visit(i+1, matching, used)
        for j in range(n):
            if j not in used and a[i][j] == 1:
                matching[i] = j
                visit(i+1, matching, used | {j})
                del matching[i]
    visit(0, {}, set())
    return best


def inspected_min_fill_rule(a):
    """Reference transcription of the inspected capped minimum-fill decision rule.

    NOT an import or execution of the native source file. Rule source:
    core_handlebody.py lines 53-106, pinned in SOURCE_AUDIT.json. Preserves
    (fill score, row size, original row id, original column id) tie breaking.
    """
    rows={i:{j:min(2,x) for j,x in enumerate(row) if x} for i,row in enumerate(a)}
    schedule=[]
    while rows:
        totals={}
        for row in rows.values():
            for c,x in row.items():totals[c]=totals.get(c,0)+x
        candidates=[((sum(row.values())-1)*(totals[c]-1),sum(row.values()),r,c)
                    for r,row in rows.items() for c,x in row.items() if x==1]
        if not candidates:break
        _,_,r,c=min(candidates);donor=rows.pop(r);donor.pop(c)
        for row in rows.values():
            factor=row.pop(c,0)
            if factor:
                for h,x in donor.items():row[h]=min(2,row.get(h,0)+factor*x)
        schedule.append([r,c])
    return schedule
