"""Contract forced potential differences and lift a full arithmetic dual.

Only zero-slack strongly connected components force equality of shifted
potentials. A one-way tight edge is not contracted. The independent checker
receives the original model and a full-sized certificate, never a quotient.
"""
from .cocycle_euler_verify import verify_difference_optimum


def _contracted_difference(n, edges, constraints, initial, check, solve):
    forward, reverse = [[] for _ in range(n)], [[] for _ in range(n)]
    for i, (a, b, d) in enumerate(constraints):
        check()
        slack = d+initial[a]-initial[b]
        if slack < 0:
            raise ValueError('initial potential violates a difference constraint')
        if slack == 0:
            forward[a].append((b, i))
            reverse[b].append((a, i))
    # Iterative Kosaraju, retaining a tree toward each component root.
    seen, order = [False]*n, []
    for root in range(n):
        check()
        if seen[root]:
            continue
        seen[root] = True
        stack = [(root, 0)]
        while stack:
            check()
            u, j = stack[-1]
            if j == len(forward[u]):
                order.append(u)
                stack.pop()
            else:
                stack[-1] = u, j+1
                v, edge = forward[u][j]
                if not seen[v]:
                    seen[v] = True
                    stack.append((v, 0))
    component, groups, inward = [-1]*n, [], [None]*n
    for root in reversed(order):
        check()
        if component[root] >= 0:
            continue
        label = len(groups)
        vertices = [root]
        component[root] = label
        for u in vertices:
            check()
            for v, edge in reverse[u]:
                check()
                if component[v] < 0:
                    component[v] = label
                    inward[v] = edge
                    vertices.append(v)
        groups.append(vertices)
    k = len(groups)
    if k == n:
        result = solve(n, edges, constraints, initial, check)
        result['stats'].update(contracted=False, input_nodes=n, quotient_nodes=n)
        return result

    # Shift p[v] = initial[v] + q[component[v]], then aggregate equivalent
    # objective terms and retain the tightest constraint per ordered pair.
    soft_groups, fixed = {}, []
    for i, (a, b, c, w) in enumerate(edges):
        check()
        u, v, cost = component[a], component[b], c+initial[b]-initial[a]
        if u == v or w == 0:
            fixed.append((i, w if cost > 0 else -w if cost < 0 else 0))
            continue
        sign = 1
        if u > v:
            u, v, cost, sign = v, u, -cost, -1
        key = u, v, cost
        soft_groups.setdefault(key, []).append((i, sign, w))
    reduced_edges, members = [], []
    for (u, v, c), rows in soft_groups.items():
        check()
        reduced_edges.append([u, v, c, sum(w for i, sign, w in rows)])
        members.append(rows)
    tightest = {}
    for i, (a, b, d) in enumerate(constraints):
        check()
        u, v = component[a], component[b]
        if u == v:
            continue
        cost = d+initial[a]-initial[b]
        if (u, v) not in tightest or cost < tightest[u, v][0]:
            tightest[u, v] = cost, i
    reduced_constraints, representatives = [], []
    for (u, v), (d, i) in tightest.items():
        check()
        reduced_constraints.append([u, v, d])
        representatives.append(i)
    result = solve(k, reduced_edges, reduced_constraints, [0]*k, check)
    quotient = result['certificate']
    values = [initial[v]+quotient['potential'][component[v]] for v in range(n)]
    offset = min(values)
    values = [v-offset for v in values]
    edge_flows, constraint_flows, balance = [0]*len(edges), [0]*len(constraints), [0]*n
    for i, flow in fixed:
        check()
        edge_flows[i] = flow
    for rows, aggregate in zip(members, quotient['edge_flows']):
        check()
        remaining = aggregate+sum(w for i, sign, w in rows)
        for i, sign, w in rows:
            check()
            amount = min(remaining, 2*w)
            edge_flows[i] = sign*(amount-w)
            remaining -= amount
        if remaining:
            raise ArithmeticError('quotient edge flow exceeds member capacity')
    for i, flow in zip(representatives, quotient['constraint_flows']):
        check()
        constraint_flows[i] = flow
    for (a, b, c, w), flow in zip(edges, edge_flows):
        check()
        balance[a] -= flow
        balance[b] += flow
    for (a, b, d), flow in zip(constraints, constraint_flows):
        check()
        balance[a] -= flow
        balance[b] += flow

    # Route positive imbalance inward, then remaining demand outward.
    # Every added flow uses an original zero-slack arc, so complementary
    # equality is preserved. Two tree traversals avoid per-unit routing.
    for vertices in groups:
        check()
        root = vertices[0]
        if sum(balance[v] for v in vertices):
            raise ArithmeticError('quotient flow does not balance a component')
        for v in reversed(vertices[1:]):
            check()
            flow = max(balance[v], 0)
            if flow:
                i = inward[v]
                a, b, d = constraints[i]
                constraint_flows[i] += flow
                balance[a] -= flow
                balance[b] += flow
        outward, parent = [root], {root: None}
        for u in outward:
            check()
            for v, edge in forward[u]:
                check()
                if component[v] == component[root] and v not in parent:
                    parent[v] = edge
                    outward.append(v)
        if len(outward) != len(vertices):
            raise ArithmeticError('zero-slack component lacks an outward tree')
        for v in reversed(outward[1:]):
            check()
            flow = -balance[v]
            if flow < 0:
                raise ArithmeticError('positive imbalance remains away from root')
            i = parent[v]
            a, b, d = constraints[i]
            constraint_flows[i] += flow
            balance[a] -= flow
            balance[b] += flow
        if balance[root]:
            raise ArithmeticError('lifted component does not balance')
    objective = 0
    for a, b, c, w in edges:
        check()
        objective += w*abs(c+values[b]-values[a])
    certificate = dict(schema='weighted-difference-optimum-v1', potential=values,
        edge_flows=edge_flows, constraint_flows=constraint_flows, objective=objective)
    if not verify_difference_optimum(n, edges, constraints, certificate, check=check):
        raise ArithmeticError('lifted Euler flow failed independent original-model replay')
    stats = dict(result['stats'], contracted=True, input_nodes=n, quotient_nodes=k,
        quotient_edges=len(reduced_edges), quotient_constraints=len(reduced_constraints),
        fixed_edges=len(fixed), flow_weight_sum=result['stats']['weight_sum'],
        weight_sum=sum(row[3] for row in edges))
    return dict(certificate=certificate, stats=stats)
