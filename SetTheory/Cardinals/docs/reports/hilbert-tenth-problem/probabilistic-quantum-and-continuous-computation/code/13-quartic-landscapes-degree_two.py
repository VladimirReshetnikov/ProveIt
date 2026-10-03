"""Exact zero counting for Boolean residual systems of interaction degree <= 2.

Input residuals are sparse integer polynomials (as in quartic_compiler).
The energy is the sum of their squares plus all Boolean penalties.
The algorithm enumerates triangle components and uses two-state transfer
matrices on paths/cycles. Its arithmetic-operation count is linear in the
number of variables and local constraints, apart from reading polynomials.
"""
from itertools import product
from quartic_compiler import Polynomial, evaluate_poly


def count_degree_two(variables: int, residuals: list[Polynomial]) -> int:
    if variables < 0:
        raise ValueError('Negative dimension.')
    adjacency = [set() for _ in range(variables)]
    scopes = []
    for p in residuals:
        scope = set(i for monomial in p for i in monomial)
        if any(i < 0 or i >= variables for i in scope):
            raise ValueError('Invalid variable in residual.')
        if not scope:
            if p.get((), 0) != 0:
                return 0
            continue
        for v in scope:
            adjacency[v].update(scope - {v})
        scopes.append((p, scope))
    if any(len(a) > 2 for a in adjacency):
        raise ValueError('Interaction degree exceeds two.')
    unvisited = set(range(variables))
    components = []
    owner = {}
    while unvisited:
        todo = [min(unvisited)]; comp = set()
        while todo:
            v = todo.pop()
            if v in comp:
                continue
            comp.add(v)
            todo.extend(adjacency[v] - comp)
        unvisited -= comp
        for v in comp:
            owner[v] = len(components)
        components.append(comp)
    local = [[] for _ in components]
    for p, scope in scopes:
        index = owner[next(iter(scope))]
        assert all(owner[v] == index for v in scope)
        local[index].append((p, scope))

    result = 1
    values = [0] * variables
    for index, comp in enumerate(components):
        constraints = local[index]
        if len(comp) <= 3:
            order = sorted(comp)
            count = 0
            for bits in product((0, 1), repeat=len(order)):
                for v, bit in zip(order, bits):
                    values[v] = bit
                count += all(evaluate_poly(p, values) == 0 for p, _ in constraints)
            result *= count
            continue
        assert all(len(scope) <= 2 for _, scope in constraints)
        unary = {v: [True, True] for v in comp}
        binary = {}
        for p, scope in constraints:
            order = sorted(scope)
            if len(order) == 1:
                v = order[0]
                for bit in (0, 1):
                    values[v] = bit
                    unary[v][bit] &= evaluate_poly(p, values) == 0
            else:
                u, v = order
                table = binary.setdefault((u, v), [[True, True], [True, True]])
                for a, b in product((0, 1), repeat=2):
                    values[u], values[v] = a, b
                    table[a][b] &= evaluate_poly(p, values) == 0

        def allowed(u, v, a, b):
            if u < v:
                return binary[(u, v)][a][b]
            return binary[(v, u)][b][a]

        endpoints = [v for v in comp if len(adjacency[v]) <= 1]
        start = min(endpoints) if endpoints else min(comp)
        is_cycle = not endpoints
        order, previous, current = [], None, start
        while True:
            order.append(current)
            successors = sorted(adjacency[current] - ({previous} if previous is not None else set()))
            if not successors:
                break
            successor = successors[0]
            if successor == start:
                break
            previous, current = current, successor
        assert len(order) == len(comp)
        count = 0
        for first in (0, 1):
            dp = [0, 0]
            dp[first] = int(unary[start][first])
            for u, v in zip(order, order[1:]):
                dp = [int(unary[v][b]) * sum(dp[a] * allowed(u, v, a, b)
                                            for a in (0, 1)) for b in (0, 1)]
            last = order[-1]
            count += sum(dp[b] * (allowed(last, start, b, first) if is_cycle else 1)
                         for b in (0, 1))
        result *= count
    return result
