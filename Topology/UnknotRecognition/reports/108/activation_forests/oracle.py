"""Bounded exponential oracles used only for independent finite validation."""

from functools import lru_cache
from itertools import combinations

from .model import parse_problem


@lru_cache(None)
def positive_pivot_eliminable(matrix):
    """Try every positive singleton pivot, including genuine positive fill."""
    if not matrix:
        return True
    height, width = len(matrix), len(matrix[0])
    for row in range(height):
        for column in range(width):
            if matrix[row][column] != 1:
                continue
            smaller = tuple(tuple(min(2, matrix[i][j]
                                      + matrix[i][column] * matrix[row][j])
                                  for j in range(width) if j != column)
                            for i in range(height) if i != row)
            if positive_pivot_eliminable(smaller):
                return True
    return False


def tree_oracle(problem, *, max_subsets=1000000, positive_pivots=False):
    """Enumerate all potential trees using explicit component relabeling.

    A capped enumeration reports INCONCLUSIVE.  Dense pivot expansion is
    explicitly bounded; huge binary column namespaces are never expanded.
    """
    data = parse_problem(problem)
    if positive_pivots and (len(data.rows) > 10 or data.columns > 10):
        raise ValueError('dense positive-pivot oracle restricted to ten by ten')
    eligible = [r for r, edge in enumerate(data.edges)
                if edge is not None and edge[0] != edge[1]]
    if data.vertices > len(eligible) + 1:
        return {'status': 'NO_FOREST', 'trees': 0, 'subsets': 0}
    attempts, trees = 0, 0
    for selected in combinations(eligible, data.vertices - 1):
        attempts += 1
        if attempts > max_subsets:
            return {'status': 'INCONCLUSIVE', 'trees': trees, 'subsets': attempts - 1}
        labels = list(range(data.vertices))
        valid = True
        for row in selected:
            a, b = [labels[v] for v in data.edges[row]]
            if a == b:
                valid = False
                break
            labels = [a if value == b else value for value in labels]
        if not valid or len(set(labels)) != 1:
            continue
        trees += 1
        live = set(range(len(data.rows))) - set(selected)
        if positive_pivots:
            matrix = tuple(tuple(dict(data.rows[row]).get(column, 0)
                                 for column in range(data.columns))
                           for row in sorted(live))
            yes = positive_pivot_eliminable(matrix)
        else:
            while live:
                totals, owners = {}, {}
                for row in live:
                    for c, a in data.rows[row]:
                        totals[c] = totals.get(c, 0) + a
                        owners[c] = row
                candidates = [c for c, a in totals.items() if a == 1]
                if not candidates:
                    break
                live.remove(owners[min(candidates)])
            yes = not live
        if yes:
            return {'status': 'SUCCESS', 'tree': list(selected),
                    'trees': trees, 'subsets': attempts}
    return {'status': 'NO_FOREST', 'trees': trees, 'subsets': attempts}
