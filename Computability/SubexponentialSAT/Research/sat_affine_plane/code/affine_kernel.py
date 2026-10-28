"""Exact finite contraction kernel for the four affine-plane plans on nine groups.

The finite evaluator uses ordinary scalar operations in Z/(2**precision).
It does not implement the asymptotic fast matrix backend or a SAT solver.
"""

from dataclasses import dataclass
from itertools import combinations, product
from math import prod


EDGES = tuple(combinations(range(9), 2))
PLANS = (
    ((0, 1, 2), (3, 4, 5), (6, 7, 8)),
    ((0, 3, 6), (1, 4, 7), (2, 5, 8)),
    ((0, 5, 7), (1, 3, 8), (2, 4, 6)),
    ((0, 4, 8), (2, 3, 7), (1, 5, 6)),
)


def validate_domains(domains):
    if len(domains) != len(EDGES):
        raise ValueError("Expected one domain size for each of the 36 unordered pairs")
    if any(type(d) is not int or d < 0 for d in domains):
        raise ValueError("Domain sizes must be nonnegative integers")
    return tuple(domains)


def assignments(indices, domains):
    return product(*(range(domains[e]) for e in indices))


def incident(vertex):
    return tuple(i for i, edge in enumerate(EDGES) if vertex in edge)


def operation_tripartitions(plan_index):
    if type(plan_index) is not int or not 0 <= plan_index < 4:
        raise ValueError("Plan index must be one of 0, 1, 2, 3")
    universe = frozenset(range(9))
    triples = []
    for line in PLANS[plan_index]:
        a, b, c = line
        triples.append((frozenset((b,)), frozenset((c,)), universe - {b, c}))
        triples.append((frozenset((a,)), frozenset((b, c)), universe - set(line)))
    triples.append(tuple(frozenset(line) for line in PLANS[plan_index]))
    return tuple(triples)


def support_vectors(plan_index):
    result = []
    for triple in operation_tripartitions(plan_index):
        part = {v: j for j, nodes in enumerate(triple) for v in nodes}
        for discounted in combinations(range(3), 2):
            result.append(tuple(
                0 if part[a] == part[b] else
                2 if tuple(sorted((part[a], part[b]))) == discounted else 5
                for a, b in EDGES
            ))
    return tuple(result)


SUPPORTS = tuple(support_vectors(j) for j in range(4))


def plan_scores(domains):
    """Return exact fifth-power work scores, or None for a zero contribution.

    Opposite directed index sets may be combined into one pair domain. Then
    log2(domains[e]) is the sum of the two directed entropies.
    """
    domains = validate_domains(domains)
    if 0 in domains:
        return None
    return tuple(max(prod(d ** v for d, v in zip(domains, support))
                     for support in menu) for menu in SUPPORTS)


def select_plan(domains):
    """Minimize the exact integer work score, breaking ties by plan index."""
    scores = plan_scores(domains)
    if scores is None:
        return None
    return min(range(4), key=lambda j: (scores[j], j))


@dataclass
class Table:
    nodes: frozenset
    boundary: tuple
    values: dict


def cache_singletons(domains, factors, modulus):
    if len(factors) != 9:
        raise ValueError("Expected nine explicit singleton factor tables")
    result = []
    for v in range(9):
        boundary = incident(v)
        keys = tuple(assignments(boundary, domains))
        if set(factors[v]) != set(keys):
            raise ValueError("Factor table does not have exactly its prescribed domain")
        if any(type(factors[v][key]) is not int for key in keys):
            raise ValueError("Factor entries must be integers")
        result.append(Table(frozenset((v,)), boundary,
                            {key: factors[v][key] % modulus for key in keys}))
    return result


def merge_tables(left, right, domains, modulus, counters):
    if left.nodes & right.nodes:
        raise ValueError("A merge must combine disjoint sets of vertices")
    nodes = left.nodes | right.nodes
    boundary = tuple(i for i, (a, b) in enumerate(EDGES)
                     if (a in nodes) != (b in nodes))
    join = tuple(i for i, (a, b) in enumerate(EDGES)
                 if (a in left.nodes and b in right.nodes) or
                    (b in left.nodes and a in right.nodes))
    values = {}
    for out_key in assignments(boundary, domains):
        current = dict(zip(boundary, out_key))
        total = 0
        for inner_key in assignments(join, domains):
            current.update(zip(join, inner_key))
            lv = left.values[tuple(current[e] for e in left.boundary)]
            rv = right.values[tuple(current[e] for e in right.boundary)]
            total = (total + lv * rv) % modulus
            counters["binary_products"] += 1
        values[out_key] = total
    return Table(nodes, boundary, values)


def close_triangle(tables, domains, modulus, counters):
    crossing = tuple(sorted(set().union(*(set(t.boundary) for t in tables))))
    total = 0
    for key in assignments(crossing, domains):
        current = dict(zip(crossing, key))
        term = 1
        for table in tables:
            term = term * table.values[tuple(current[e] for e in table.boundary)] % modulus
        total = (total + term) % modulus
        counters["triangle_terms"] += 1
    return total


def contract(domains, factors, precision, plan_index=None):
    """Contract an explicit nine-factor graph exactly modulo 2**precision.

    If plan_index is None, use the exact selector. Domain-zero inputs have
    value zero and do not evaluate any factors, including missing factors.
    """
    domains = validate_domains(domains)
    if type(precision) is not int or precision < 1:
        raise ValueError("Precision must be a positive integer")
    counters = {"cached_entries": 0, "binary_products": 0, "triangle_terms": 0}
    if 0 in domains:
        return {"value": 0, "plan": None, "score": None, **counters}
    if plan_index is None:
        plan_index = select_plan(domains)
    operation_tripartitions(plan_index)
    modulus = 1 << precision
    singletons = cache_singletons(domains, factors, modulus)
    counters["cached_entries"] = sum(len(t.values) for t in singletons)
    lines = []
    for a, b, c in PLANS[plan_index]:
        pair = merge_tables(singletons[b], singletons[c], domains, modulus, counters)
        lines.append(merge_tables(singletons[a], pair, domains, modulus, counters))
    answer = close_triangle(lines, domains, modulus, counters)
    return {"value": answer, "plan": plan_index,
            "score": plan_scores(domains)[plan_index], **counters}


def brute_force(domains, factors, precision):
    """Independent direct sum over all edge assignments for small verification."""
    domains = validate_domains(domains)
    if type(precision) is not int or precision < 1:
        raise ValueError("Precision must be a positive integer")
    if 0 in domains:
        return 0
    if len(factors) != 9:
        raise ValueError("Expected nine factors")
    mod = 1 << precision
    incident_edges = [incident(v) for v in range(9)]
    total = 0
    for setting in product(*(range(d) for d in domains)):
        term = 1
        for v in range(9):
            key = tuple(setting[e] for e in incident_edges[v])
            term *= factors[v][key]
        total = (total + term) % mod
    return total
