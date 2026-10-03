"""Direct finite-support component simulator for the binary planar shuttle.

Only this module uses connected components. The local evaluator is separately
implemented in local_rule.py and does not import this module.
"""

RULES = {
    ((0, 0), (1, 0)): ((1, 0), (2, 0)),
    ((0, 0), (2, 0)): ((-1, 0), (1, 0)),
    ((0, 0), (1, 0), (3, 0)): ((-1, 0), (1, 0), (4, 1)),
    ((0, 0), (2, 0), (4, 0)): ((0, 1), (3, 1), (4, 1)),
}


def components(support):
    remaining = set(support)
    while remaining:
        root = min(remaining)
        remaining.remove(root)
        component = {root}
        queue = [root]
        while queue:
            x, y = queue.pop()
            for u in range(x - 2, x + 3):
                for v in range(y - 2, y + 3):
                    p = (u, v)
                    if p in remaining:
                        remaining.remove(p)
                        component.add(p)
                        queue.append(p)
        yield component


def step(support):
    output = set()
    for component in components(support):
        ax = min(x for x, _ in component)
        ay = min(y for _, y in component)
        normalized = tuple(sorted((x - ax, y - ay) for x, y in component))
        replacement = RULES.get(normalized, normalized)
        emitted = {(ax + x, ay + y) for x, y in replacement}
        if output & emitted:
            raise RuntimeError("Distinct components emitted colliding particles")
        if len(emitted) != len(component):
            raise RuntimeError("A rewrite changed mass")
        output.update(emitted)
    return output


def drift_step(support):
    return {(x, y + 1) for x, y in step(support)}


def initial(k):
    if type(k) is not int or k < 7:
        raise ValueError("k must be an integer at least 7")
    return {(0, 0), (3, 0), (4, 0), (k, 0)}


def section_time(k, n):
    if type(k) is not int or k < 7 or type(n) is not int or n < 0:
        raise ValueError("k >= 7 and n >= 0 must be integers")
    return n * n + (2 * k - 11) * n


def phase_support(k, n, j):
    """Support at T_n+j, 0 <= j < 2(k+n)-10 (half-open cycle)."""
    section_time(k, n)
    d = k + n
    if type(j) is not int or not 0 <= j < 2 * d - 10:
        raise ValueError("j is outside the half-open cycle")
    if j <= d - 6:
        return {(0, n), (3 + j, n), (4 + j, n), (d, n)}
    q = j - (d - 5)
    return {(0, n), (d - 4 - q, n), (d - 2 - q, n), (d + 1, n + 1)}
