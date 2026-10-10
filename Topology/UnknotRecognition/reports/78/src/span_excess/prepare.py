"""Small exact reference producer of balanced span witnesses.

A standard Hungarian assignment selects lower/upper corners meeting at the
same global vertex. Feasibility plus primal-dual equality is checked after
selection. This is auxiliary preparation, not a new minimum-span algorithm.
"""
from .model import HeightModel, noop
from .network import feasibility
from .strata import Stratum, constraints_for


def _assignment(cost, check=noop):
    n = len(cost)
    u, v, p, way = [0]*(n+1), [0]*(n+1), [0]*(n+1), [0]*(n+1)
    for i in range(1, n+1):
        p[0] = i
        j0 = 0
        minimum, used = [None]*(n+1), [False]*(n+1)
        while True:
            check()
            used[j0] = True
            i0, delta, j1 = p[j0], None, None
            for j in range(1, n+1):
                if used[j]:
                    continue
                cur = cost[i0-1][j-1]-u[i0]-v[j]
                if minimum[j] is None or cur < minimum[j]:
                    minimum[j], way[j] = cur, j0
                if delta is None or minimum[j] < delta:
                    delta, j1 = minimum[j], j
            for j in range(n+1):
                if used[j]:
                    u[p[j]] += delta
                    v[j] -= delta
                elif minimum[j] is not None:
                    minimum[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while True:
            j1 = way[j0]
            p[j0] = p[j1]
            j0 = j1
            if j0 == 0:
                break
    return [(p[j]-1, j-1) for j in range(1, n+1)]


def prepare_model(n, vertices, heights, edges=(), check=noop):
    vertices, heights = tuple(map(tuple, vertices)), tuple(map(tuple, heights))
    t = len(vertices)
    if t == 0 or len(heights) != t:
        raise ValueError("nonempty equally sized arrays required")
    pairs, weights = {}, [[None]*t for _ in range(t)]
    C = 0
    for i in range(t):
        for j in range(t):
            for a in range(4):
                for b in range(4):
                    check()
                    if vertices[i][a] != vertices[j][b]:
                        continue
                    w = heights[j][b]-heights[i][a]
                    if weights[i][j] is None or w > weights[i][j]:
                        weights[i][j], pairs[i, j] = w, (a, b)
                        C = max(C, abs(w))
    forbidden = (2*t+1)*(C+1)
    cost = [[forbidden if w is None else -w for w in row] for row in weights]
    assignment = _assignment(cost, check)
    low, high = [None]*t, [None]*t
    optimum = 0
    for i, j in assignment:
        if (i, j) not in pairs:
            raise ArithmeticError("diagonal choices guarantee a perfect assignment")
        low[i], high[j] = pairs[i, j]
        optimum += weights[i][j]
    dummy = HeightModel(n, vertices, heights, tuple(low), tuple(high), optimum,
                        (0,)*n, tuple(map(tuple, edges)))
    arcs = constraints_for(dummy, Stratum())
    result = feasibility(n, arcs, check)
    if result['status'] != 'FEASIBLE':
        raise ArithmeticError("maximum assignment has no attaining span potential")
    p = result['potential']
    base = min(p)
    model = HeightModel(n, vertices, heights, tuple(low), tuple(high), optimum,
                        tuple(x-base for x in p), tuple(map(tuple, edges)))
    model.validate()
    return model
