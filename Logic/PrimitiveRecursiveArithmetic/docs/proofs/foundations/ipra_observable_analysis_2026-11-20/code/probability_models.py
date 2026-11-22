#!/usr/bin/env python3
"""Exact finite kernels for a represented Wasserstein probability sort.

Only Python's standard library is used.  Fraction arithmetic is exact.
The forest enumerator is deliberately a bounded completeness baseline,
not an efficient general-purpose transport solver.  A faster producer can
submit a rational primal/dual certificate to verify_transport_certificate.

Running this file checks nontrivial examples and emits their exact values.
The mathematical correctness proofs are in model_probability.tex; these
tests do not establish a formal iPRA translation or an infinite theorem.
"""

from __future__ import annotations

from fractions import Fraction as Q
from itertools import product
import json


def _validate_marginals(a, b):
    a, b = tuple(map(Q, a)), tuple(map(Q, b))
    if not a or not b or any(x < 0 for x in a + b):
        raise ValueError("Nonempty nonnegative marginals required")
    if sum(a) != 1 or sum(b) != 1:
        raise ValueError("Each marginal must sum exactly to one")
    return a, b


def _forest_coupling(a, b, mask):
    """Unique coupling on a candidate forest, or None if infeasible/cyclic."""
    p, q = len(a), len(b)
    parent = list(range(p + q))

    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v

    edges = []
    adjacency = [set() for _ in range(p + q)]
    for i in range(p):
        for j in range(q):
            edge = i * q + j
            if not (mask >> edge) & 1:
                continue
            u, v = root(i), root(p + j)
            if u == v:
                return None
            parent[u] = v
            edges.append(edge)
            adjacency[i].add(edge)
            adjacency[p + j].add(edge)

    residual = list(a + b)
    coupling = [[Q(0) for _ in b] for _ in a]
    remaining = set(edges)
    for _ in edges:
        leaf = next(v for v in range(p + q) if len(adjacency[v]) == 1)
        edge = next(iter(adjacency[leaf]))
        i, j = divmod(edge, q)
        neighbor = p + j if leaf == i else i
        value = residual[leaf]
        if value < 0 or value > residual[neighbor]:
            return None
        coupling[i][j] = value
        residual[neighbor] -= value
        residual[leaf] = 0
        adjacency[i].remove(edge)
        adjacency[p + j].remove(edge)
        remaining.remove(edge)
    if remaining or any(residual):
        return None
    return tuple(tuple(row) for row in coupling)


def finite_transport(a, b, costs):
    """Minimum rational transport cost, by all 2^(p*q) support masks."""
    a, b = _validate_marginals(a, b)
    p, q = len(a), len(b)
    costs = tuple(tuple(map(Q, row)) for row in costs)
    if len(costs) != p or any(len(row) != q for row in costs):
        raise ValueError("Cost matrix has the wrong dimensions")
    if any(c < 0 for row in costs for c in row):
        raise ValueError("Nonnegative metric costs required")
    best = None
    feasible_forests = 0
    for mask in range(1 << (p * q)):
        coupling = _forest_coupling(a, b, mask)
        if coupling is None:
            continue
        feasible_forests += 1
        cost = sum(coupling[i][j] * costs[i][j]
                   for i in range(p) for j in range(q))
        if best is None or cost < best["cost"]:
            best = {"cost": cost, "coupling": coupling, "support_mask": mask}
    if best is None:
        raise AssertionError("Feasible probability marginals must have a forest coupling")
    best["masks_examined"] = 1 << (p * q)
    best["feasible_forests"] = feasible_forests
    return best


def verify_transport_certificate(a, b, costs, coupling, alpha, beta):
    """Check a rational primal/dual equality certificate; no LP solver used."""
    a, b = _validate_marginals(a, b)
    costs = tuple(tuple(map(Q, row)) for row in costs)
    coupling = tuple(tuple(map(Q, row)) for row in coupling)
    alpha, beta = tuple(map(Q, alpha)), tuple(map(Q, beta))
    p, q = len(a), len(b)
    if len(coupling) != p or any(len(row) != q for row in coupling):
        return False
    if len(costs) != p or any(len(row) != q for row in costs):
        return False
    if len(alpha) != p or len(beta) != q:
        return False
    if any(x < 0 for row in coupling for x in row):
        return False
    if any(sum(coupling[i]) != a[i] for i in range(p)):
        return False
    if any(sum(coupling[i][j] for i in range(p)) != b[j] for j in range(q)):
        return False
    if any(alpha[i] + beta[j] > costs[i][j] for i in range(p) for j in range(q)):
        return False
    primal = sum(coupling[i][j] * costs[i][j] for i in range(p) for j in range(q))
    dual = sum(alpha[i] * a[i] for i in range(p)) + sum(beta[j] * b[j] for j in range(q))
    return primal == dual


def glue_couplings(pi, sigma, middle):
    """Finite gluing, treating zero middle marginal explicitly."""
    pi = tuple(tuple(map(Q, row)) for row in pi)
    sigma = tuple(tuple(map(Q, row)) for row in sigma)
    middle = tuple(map(Q, middle))
    if not pi or not sigma or not sigma[0] or any(x < 0 for x in middle):
        raise ValueError("Nonempty nonnegative coupling data required")
    p, q, r = len(pi), len(middle), len(sigma[0])
    if len(sigma) != q or any(len(row) != q for row in pi) or any(len(row) != r for row in sigma):
        raise ValueError("Incompatible dimensions")
    if any(x < 0 for row in pi + sigma for x in row):
        raise ValueError("Coupling entries must be nonnegative")
    if any(sum(pi[i][j] for i in range(p)) != middle[j] for j in range(q)):
        raise ValueError("Left coupling has the wrong middle marginal")
    if any(sum(sigma[j]) != middle[j] for j in range(q)):
        raise ValueError("Right coupling has the wrong middle marginal")
    for j, mass in enumerate(middle):
        if mass == 0:
            if any(pi[i][j] != 0 for i in range(p)) or any(sigma[j][k] != 0 for k in range(r)):
                raise ValueError("Zero middle mass has nonzero incident flow")
    return tuple(tuple(sum(pi[i][j] * sigma[j][k] / middle[j]
                           for j in range(q) if middle[j] > 0)
                       for k in range(r)) for i in range(p))


def atomic_distance(xs, a, ys, b):
    return finite_transport(a, b, [[abs(x - y) for y in ys] for x in xs])


def probability_net(centers, denominator):
    """All genuine probability laws with this denominator on these centers."""
    if not centers or denominator < 1:
        raise ValueError("Nonempty centers and a positive denominator required")
    for numerators in product(range(denominator + 1), repeat=len(centers)):
        if sum(numerators) == denominator:
            yield tuple(Q(a, denominator) for a in numerators)


def push_and_round(xs, a, centers, radius, denominator):
    """Explicit selector for the dense atomic-law probability net."""
    a, _ = _validate_marginals(a, (Q(1),))
    xs, centers, radius = tuple(map(Q, xs)), tuple(map(Q, centers)), Q(radius)
    if len(xs) != len(a) or not centers or denominator < 1:
        raise ValueError("Invalid atomic law or net")
    masses = [Q(0) for _ in centers]
    push_cost = Q(0)
    for x, mass in zip(xs, a):
        candidates = [i for i, c in enumerate(centers) if abs(x - c) <= radius]
        if not candidates:
            raise ValueError("Supplied centers fail the requested cover on this input")
        i = candidates[0]
        masses[i] += mass
        push_cost += mass * abs(x - centers[i])
    numerators = [(denominator * w).numerator // (denominator * w).denominator
                  for w in masses[:-1]]
    numerators.append(denominator - sum(numerators))
    rounded = tuple(Q(k, denominator) for k in numerators)
    round_cost = sum((masses[i] - rounded[i]) * abs(centers[i] - centers[-1])
                     for i in range(len(centers) - 1))
    tv = sum(abs(masses[i] - rounded[i]) for i in range(len(centers))) / 2
    return {"weights": rounded, "pushed_weights": tuple(masses),
            "push_cost": push_cost, "round_cost": round_cost, "tv": tv}


def moment_objective(xs, weights):
    xs, weights = tuple(map(Q, xs)), tuple(map(Q, weights))
    mean = sum(w * x for x, w in zip(xs, weights))
    second = sum(w * x * x for x, w in zip(xs, weights))
    return max(abs(mean - Q(1, 2)), abs(second - Q(3, 4)))


def checks():
    xs = (Q(0), Q(1))
    a, b = (Q(1, 4), Q(3, 4)), (Q(1, 2), Q(1, 2))
    costs = ((Q(0), Q(1)), (Q(1), Q(0)))
    transport = finite_transport(a, b, costs)
    assert transport["cost"] == Q(1, 4)
    assert verify_transport_certificate(a, b, costs, transport["coupling"],
                                        (Q(0), Q(1)), (Q(0), Q(-1)))
    assert not verify_transport_certificate(a, b, costs, transport["coupling"],
                                            (Q(1), Q(1)), (Q(0), Q(0)))

    # Gluing with an actual zero middle marginal; compare all three exact minima.
    mids, middle = (Q(0), Q(1, 2), Q(1)), (Q(1, 2), Q(0), Q(1, 2))
    zs, c = (Q(1, 4), Q(3, 4)), (Q(2, 3), Q(1, 3))
    xy = atomic_distance(xs, a, mids, middle)
    yz = atomic_distance(mids, middle, zs, c)
    xz = atomic_distance(xs, a, zs, c)
    glued = glue_couplings(xy["coupling"], yz["coupling"], middle)
    assert tuple(sum(row) for row in glued) == a
    assert tuple(sum(row[k] for row in glued) for k in range(len(c))) == c
    glued_cost = sum(glued[i][k] * abs(xs[i] - zs[k])
                     for i in range(len(a)) for k in range(len(c)))
    assert xz["cost"] <= glued_cost <= xy["cost"] + yz["cost"]

    # A non-grid law, pushed and rounded into a 45-member denominator-8 net.
    points = (Q(1, 8), Q(1, 3), Q(7, 8))
    masses = (Q(2, 7), Q(1, 7), Q(4, 7))
    centers, denominator, radius = (Q(0), Q(1, 2), Q(1)), 8, Q(1, 4)
    selected = push_and_round(points, masses, centers, radius, denominator)
    net = list(probability_net(centers, denominator))
    assert len(net) == 45 and selected["weights"] in net
    assert selected["push_cost"] <= radius
    assert selected["tv"] <= Q(len(centers) - 1, denominator)
    assert selected["round_cost"] <= selected["tv"]  # diameter is one
    selected_distance = atomic_distance(points, masses, centers, selected["weights"])["cost"]
    assert selected_distance <= selected["push_cost"] + selected["round_cost"] <= Q(1, 2)

    # Exact finite witness for the proved continuum/probability-sort optimum.
    endpoint_net = list(probability_net(xs, 8))
    optimizer = min(endpoint_net, key=lambda weights: moment_objective(xs, weights))
    assert optimizer == (Q(3, 8), Q(5, 8))
    assert moment_objective(xs, optimizer) == Q(1, 8)
    assert min(moment_objective(centers, w) for w in net) == Q(1, 8)

    return {
        "arithmetic": "fractions.Fraction (exact)",
        "transport_two_points": str(transport["cost"]),
        "transport_masks_examined": transport["masks_examined"],
        "primal_dual_certificate": "accepted; altered invalid certificate rejected",
        "zero_marginal_gluing": "passed",
        "triangle_distances": list(map(str, (xy["cost"], yz["cost"], xz["cost"]))),
        "probability_net_size": len(net),
        "selected_net_law": list(map(str, selected["weights"])),
        "selected_transport_distance": str(selected_distance),
        "moment_infimum": "1/8",
        "attaining_endpoint_weights": list(map(str, optimizer)),
        "scope": "Finite implementation checks, not an iPRA proof or a general measure construction",
    }


if __name__ == "__main__":
    print(json.dumps(checks(), indent=2))
