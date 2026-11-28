#!/usr/bin/env python3
"""Exact finite checks for symmetric edge polytopes. Python 3.9+, standard library."""

from fractions import Fraction
from functools import reduce
from math import comb, gcd, lcm


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def partitions(n, least=1):
    """Unordered partitions with parts at least least."""
    if n == 0:
        yield ()
    for i in range(least, n + 1):
        for tail in partitions(n - i, i):
            yield (i,) + tail


def gamma(parts):
    d = sum(parts) - 1
    result = []
    for j in range(d // 2 + 1):
        tail = sum(choose(a, ell) * choose(d - a, 2*j - ell)
                   for a in parts for ell in range(j + 1, 2*j + 1))
        result.append(choose(2*j, j) * (choose(d, 2*j) - tail))
    return result


def recover_parts(d, coefficients):
    """Invert the gamma formula with dimension d known."""
    largest_j = d // 2
    degree = max(j for j, coefficient in enumerate(coefficients) if coefficient)
    recovered = []
    if degree < largest_j:
        recovered.append(d - degree)
    for j in range(largest_j, 0, -1):
        deficit = choose(d, 2*j) - coefficients[j] // choose(2*j, j)
        for a in recovered:
            deficit -= sum(choose(a, ell) * choose(d - a, 2*j - ell)
                           for ell in range(j + 1, 2*j + 1))
        diagonal = choose(d - j - 1, j - 1)
        multiplicity, remainder = divmod(deficit, diagonal)
        checked(multiplicity >= 0 and remainder == 0, (j, deficit, diagonal))
        recovered.extend([j + 1] * multiplicity)
    singleton_count = d + 1 - sum(recovered)
    checked(singleton_count >= 0, recovered)
    return tuple(sorted(recovered + [1] * singleton_count))


def h_star(d, coefficients):
    return [sum(g * choose(d - 2*j, k - j) for j, g in enumerate(coefficients))
            for k in range(d + 1)]


def ehrhart_at(d, h, radius):
    return sum(value * choose(radius + d - k, d) for k, value in enumerate(h))


def balls_by_edges(parts, max_radius):
    """Breadth-first search with both orientations of every multipartite edge.

    A base-b integer encodes the first v-1 coordinates; the last is minus
    their sum. With b > 2*max_radius, encodings are distinct throughout the
    tested boxes. Network-flow integrality identifies these word balls with
    lattice points in the dilates.
    """
    v = sum(parts)
    labels = [i for i, a in enumerate(parts) for _ in range(a)]
    base = 2 * max_radius + 1
    basis = [base**k for k in range(v - 1)] + [0]
    steps = [basis[i] - basis[j] for i in range(v) for j in range(v)
             if labels[i] != labels[j]]
    visited = {0}
    frontier = {0}
    sizes = [1]
    for _ in range(max_radius):
        frontier = {x + step for x in frontier for step in steps} - visited
        visited.update(frontier)
        sizes.append(len(visited))
    return sizes


def crosspolytope(d, radius):
    """Ehrhart count by choosing support size, signs, positive magnitudes."""
    return sum(2**k * choose(d, k) * choose(radius, k)
               for k in range(min(d, radius) + 1))


def centered_transform(d, h):
    """Coefficients of i^(-d) 2^d d! E((-1+i*y)/2), in increasing powers."""
    raw = [0] * (d + 1)
    for k, h_k in enumerate(h):
        basis = [1]
        for r in range(1, d + 1):
            constant = 2*r - 1 - 2*k
            basis = [constant * a + b for a, b in
                     zip(basis + [0], [0] + basis)]
        for j, coefficient in enumerate(basis):
            raw[j] += h_k * coefficient
    assert all(raw[j] == 0 for j in range(1 - d % 2, d + 1, 2))
    return [a * (-1 if (j - d) % 4 == 2 else 1) for j, a in enumerate(raw)]


def primitive(coefficients):
    """Remove only positive content; preserve all signs in Sturm's chain."""
    values = list(map(Fraction, coefficients))
    while values and values[-1] == 0:
        values.pop()
    if not values:
        return []
    common = reduce(lcm, (a.denominator for a in values), 1)
    scaled = [int(a * common) for a in values]
    content = reduce(gcd, (abs(a) for a in scaled), 0)
    return [a // content for a in scaled]


def negative_remainder(first, second):
    work = list(map(Fraction, first))
    while len(work) >= len(second):
        shift = len(work) - len(second)
        quotient = work[-1] / second[-1]
        for j, coeff in enumerate(second):
            work[j + shift] -= quotient * coeff
        while work and work[-1] == 0:
            work.pop()
    return primitive([-a for a in work])


def sturm(polynomial):
    chain = [primitive(polynomial)]
    chain.append(primitive([k*a for k, a in enumerate(chain[0]) if k]))
    while chain[-1]:
        chain.append(negative_remainder(chain[-2], chain[-1]))
    return chain[:-1]


def variations(values):
    signs = [a > 0 for a in values if a != 0]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def checked(condition, info):
    if not condition:
        raise AssertionError(info)


def main():
    graph_count = 0
    counts = 0
    for v in range(2, 9):
        d = v - 1
        radius = (d + 1) if v <= 6 else (d // 2 + 1)
        for parts in partitions(v):
            if len(parts) < 2:
                continue
            graph_count += 1
            h = h_star(d, gamma(parts))
            direct = balls_by_edges(parts, radius)
            predicted = [ehrhart_at(d, h, r) for r in range(radius + 1)]
            checked(direct == predicted, (parts, direct, predicted))
            counts += radius + 1
    print(f"Edge-step BFS: {graph_count} multipartitions of orders 2 through 8, "
          f"{counts} ball counts agree.")
    print("Radii 0 through v for v <= 6, and 0 through floor((v-1)/2)+1 otherwise.")

    tested = 0
    for v in range(2, 25):
        d = v - 1
        for parts in partitions(v):
            if len(parts) < 2:
                continue
            g = gamma(parts)
            expected = min(d // 2, d - max(parts))
            checked(all(x > 0 for x in g[:expected + 1]) and
                    all(x == 0 for x in g[expected + 1:]), (parts, g, expected))
            checked(recover_parts(d, g) == parts, (parts, g))
            tested += 1
    print(f"Nonnegativity, no gaps and exact gamma degree: {tested} multipartitions "
          "of orders 2 through 24 agree.")

    example = (1, 2, 2, 3, 12)
    egamma = gamma(example)
    print(f"Exact inverse reconstruction: all {tested} multipartitions recovered.")
    print(f"  Dimension 19, gamma = {egamma}; recovered {recover_parts(19, egamma)}.")

    tested = 0
    for v in range(3, 25):
        d = v - 1
        h_complete = h_star(d, gamma((1,) * v))
        for m in range(1, v // 2 + 1):
            parts = (1,) * (v - 2*m) + (2,) * m
            if len(parts) < 2:
                continue
            actual = h_star(d, gamma(parts))
            for r in range(d + 1):
                lhs = 2 * ehrhart_at(d, actual, r)
                rhs = (2 * ehrhart_at(d, h_complete, r)
                       - m * (crosspolytope(d, r) - crosspolytope(d - 2, r)))
                checked(lhs == rhs, (parts, r, lhs, rhs))
                tested += 1
    print(f"Matching-deletion identity: {tested} integer evaluations, v=3 through 24, "
          "every matching size >= 1, radii 0 through v-1.")

    parts = (2,) * 6
    d = sum(parts) - 1
    g = gamma(parts)
    h = h_star(d, g)
    transformed = centered_transform(d, h)
    p = primitive(transformed[1::2])
    chain = sturm(p)
    signed_at_zero = [s[0] for s in chain]
    signed_at_infinity = [s[-1] for s in chain]
    signed_at_minus_infinity = [s[-1] * (-1)**(len(s) - 1) for s in chain]
    v_minus = variations(signed_at_minus_infinity)
    v_zero = variations(signed_at_zero)
    v_plus = variations(signed_at_infinity)
    checked(p[0] != 0 and len(chain[-1]) == 1, "zero or repeated root")
    cl_roots = 1 + 2 * (v_zero - v_plus)
    checked(cl_roots < d, (cl_roots, d))
    print("Davis graph K_{2,2,2,2,2,2}:")
    print("  gamma =", g)
    print("  h*    =", h)
    print("  Primitive P(T), coefficient order constant first =", p)
    print("  P(y^2) times y is proportional to i^(-11) E((-1+i*y)/2).")
    print("  Sturm variations at -infinity, 0, +infinity =", (v_minus, v_zero, v_plus))
    print(f"  Degree {d}: {cl_roots} roots on the canonical line, {d-cl_roots} off.")
    print("All exact checks passed.")


if __name__ == "__main__":
    main()
