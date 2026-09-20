"""Finite, exact tools for the binary-DFAO reversal obstruction.

Python 3.10+, standard library only.  Transformations are tuples on range(n).
Composition is ordinary function composition; pullback(c, t) is c o t.
The mathematical proof in the article does not depend on this implementation.
"""
from __future__ import annotations
from collections import deque
from itertools import permutations
from math import factorial, gcd, lcm
from typing import Iterable, Sequence

Map = tuple[int, ...]
Edge = tuple[int, int]


def validate_map(t: Sequence[int], n: int | None = None) -> Map:
    t = tuple(t)
    n = len(t) if n is None else n
    if n <= 0 or len(t) != n or any(type(x) is not int or not 0 <= x < n for x in t):
        raise ValueError("A transformation must be a nonempty tuple on range(n).")
    return t


def validate_colors(c: Sequence[int], n: int, k: int) -> Map:
    c = tuple(c)
    if k < 1 or len(c) != n or any(type(x) is not int or not 0 <= x < k for x in c):
        raise ValueError("Invalid output map.")
    return c


def pullback(c: Sequence[int], t: Sequence[int]) -> Map:
    return tuple(c[x] for x in t)


def is_permutation(t: Sequence[int]) -> bool:
    return sorted(t) == list(range(len(t)))


def cycles(a: Sequence[int]) -> list[Map]:
    a = validate_map(a)
    if not is_permutation(a):
        raise ValueError("Expected a permutation.")
    remaining = set(range(len(a)))
    result = []
    while remaining:
        v = min(remaining)
        component = []
        while v in remaining:
            remaining.remove(v)
            component.append(v)
            v = a[v]
        result.append(tuple(component))
    return result


def permutation_order(a: Sequence[int]) -> int:
    result = 1
    for cyc in cycles(a):
        result = lcm(result, len(cyc))
    return result


def partitions(n: int, lower: int = 1) -> Iterable[Map]:
    if n == 0:
        yield ()
    for first in range(lower, n + 1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def landau(k: int) -> int:
    """Largest order in S_k, by integer partitions (not for huge k)."""
    if not 1 <= k <= 60:
        raise ValueError("This exact partition implementation supports 1 <= k <= 60.")
    return max(lcm(*part) for part in partitions(k))


def reverse_orbit(generators: Sequence[Sequence[int]], tau: Sequence[int],
                  k: int, max_states: int = 1_000_000) -> dict[Map, str]:
    if not generators:
        raise ValueError("At least one generator is required.")
    n = len(tau)
    gens = [validate_map(t, n) for t in generators]
    initial = validate_colors(tau, n, k)
    if len(gens) > 26:
        raise ValueError("Word labels currently support at most 26 generators.")
    seen = {initial: ""}
    queue = deque([initial])
    while queue:
        c = queue.popleft()
        for i, t in enumerate(gens):
            d = pullback(c, t)
            if d not in seen:
                if len(seen) >= max_states:
                    raise RuntimeError("Orbit limit reached; no partial result returned.")
                seen[d] = seen[c] + chr(97 + i)
                queue.append(d)
    return seen


def collision(t: Sequence[int]) -> Edge:
    positions: dict[int, int] = {}
    for q, image in enumerate(t):
        if image in positions:
            return positions[image], q
        positions[image] = q
    raise ValueError("A permutation has no collision pair.")


def orbital_edges(a: Sequence[int], pair: Edge) -> tuple[Edge, ...]:
    a = validate_map(a)
    if not is_permutation(a):
        raise ValueError("Expected a permutation.")
    u, v = pair
    if u == v or not (0 <= u < len(a) and 0 <= v < len(a)):
        raise ValueError("Expected two distinct vertices.")
    seen: set[Edge] = set()
    edge = tuple(sorted((u, v)))
    while edge not in seen:
        seen.add(edge)
        edge = tuple(sorted((a[edge[0]], a[edge[1]])))
    return tuple(sorted(seen))


def proper(c: Sequence[int], edges: Sequence[Edge]) -> bool:
    return all(c[u] != c[v] for u, v in edges)


def three_coloring(n: int, edges: Sequence[Edge]) -> Map:
    """For a bipartite graph or a graph of maximum degree two; uses all 3 colors."""
    if n < 3:
        raise ValueError("Three distinct colors require at least three vertices.")
    adjacency = [set() for _ in range(n)]
    for u, v in edges:
        if u == v or not (0 <= u < n and 0 <= v < n):
            raise ValueError("Invalid simple-graph edge.")
        adjacency[u].add(v)
        adjacency[v].add(u)
    c = [-1] * n
    bipartite = True
    for root in range(n):
        if c[root] != -1:
            continue
        c[root] = 0
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in sorted(adjacency[u]):
                if c[v] == -1:
                    c[v] = 1 - c[u]
                    queue.append(v)
                elif c[v] == c[u]:
                    bipartite = False
    if not bipartite:
        if any(len(neighbors) > 2 for neighbors in adjacency):
            raise ValueError("Outside the proved three-colorable graph classes.")
        c = [-1] * n
        for u in range(n):
            excluded = {c[v] for v in adjacency[u]}
            c[u] = next(x for x in range(3) if x not in excluded)
    for new_color in sorted(set(range(3)) - set(c)):
        u = next(i for i in range(n) if c.count(c[i]) >= 2)
        c[u] = new_color
    if set(c) != {0, 1, 2} or not proper(c, edges):
        raise AssertionError("Internal coloring invariant failed.")
    return tuple(c)


def refine_coloring(c: Sequence[int], k: int) -> Map:
    c = list(c)
    used = set(c)
    if used != set(range(len(used))) or len(used) > k or k > len(c):
        raise ValueError("Expected contiguous color names and |image| <= k <= n.")
    for new_color in range(len(used), k):
        u = next(i for i in range(len(c)) if c.count(c[i]) >= 2)
        c[u] = new_color
    return tuple(c)


def cyclic_membership(a: Sequence[int], tau: Sequence[int], target: Sequence[int]) -> dict:
    """Decide target = tau o a^j by cyclic strings and generalized CRT.

    Returns constraints and either an exponent or a locally checkable obstruction.
    It never enumerates the (potentially very large) order of a.
    """
    a = validate_map(a)
    n = len(a)
    if len(tau) != n or len(target) != n:
        raise ValueError("Mismatched dimensions.")
    residue, modulus = 0, 1
    constraints = []
    for cyc in cycles(a):
        x = [tau[v] for v in cyc]
        y = [target[v] for v in cyc]
        size = len(cyc)
        shifts = [j for j in range(size)
                  if all(y[i] == x[(i + j) % size] for i in range(size))]
        if not shifts:
            return {"member": False, "reason": "no_rotation", "cycle": list(cyc),
                    "constraints": constraints}
        period = next(d for d in range(1, size + 1)
                      if all(x[i] == x[(i + d) % size] for i in range(size)))
        r = shifts[0] % period
        if shifts != [j for j in range(size) if j % period == r]:
            raise AssertionError("Rotation-coset invariant failed.")
        constraints.append({"cycle": list(cyc), "residue": r, "modulus": period})
        g = gcd(modulus, period)
        if (r - residue) % g:
            return {"member": False, "reason": "inconsistent_CRT",
                    "old_residue": residue, "old_modulus": modulus,
                    "new_residue": r, "new_modulus": period,
                    "constraints": constraints}
        reduced = period // g
        step = 0 if reduced == 1 else (
            (r - residue) // g * pow(modulus // g, -1, reduced)) % reduced
        residue += modulus * step
        modulus = lcm(modulus, period)
        residue %= modulus
    return {"member": True, "exponent": residue, "modulus": modulus,
            "constraints": constraints}


def missing_certificate(a: Sequence[int], b: Sequence[int], tau: Sequence[int], k: int) -> dict:
    """Construct an unreachable reverse-state certificate in polynomial time."""
    a = validate_map(a)
    n = len(a)
    b = validate_map(b, n)
    tau = validate_colors(tau, n, k)
    if not 3 <= k <= n:
        raise ValueError("The theorem assumes 3 <= k <= n.")
    cert = {"n": n, "k": k, "a": list(a), "b": list(b), "tau": list(tau)}
    pa, pb = is_permutation(a), is_permutation(b)
    if pa and pb:
        color = 1 if len(set(tau)) == 1 and tau[0] == 0 else 0
        target = (color,) * n
        cert.update(case="two_permutations", target=list(target))
        return cert
    if not pa and not pb:
        edges = (collision(a), collision(b))
        base = three_coloring(n, edges)
        target = next(tuple(p[x] for x in base) for p in permutations(range(3))
                      if tuple(p[x] for x in base) != tau)
        cert.update(case="two_singular", pairs=[list(e) for e in edges], target=list(target))
        return cert
    perm, singular = (a, b) if pa else (b, a)
    pair = collision(singular)
    edges = orbital_edges(perm, pair)
    base = three_coloring(n, edges)
    for p in permutations(range(3)):
        target = tuple(p[x] for x in base)
        result = cyclic_membership(perm, tau, target)
        if not result["member"]:
            cert.update(case="one_permutation", permutation_letter="a" if pa else "b",
                        pair=list(pair), edges=[list(e) for e in edges],
                        target=list(target), cyclic_nonmembership=result)
            return cert
    raise AssertionError("Cyclic relabeling lemma violated.")


def stirling_second(n: int, r: int) -> int:
    row = [1] + [0] * r
    for _ in range(n):
        row = [0] + [row[j - 1] + j * row[j] for j in range(1, r + 1)]
    return row[r]


def bipartite_chromatic(p: int, q: int, k: int) -> int:
    return sum(factorial(k) // factorial(k-r) * stirling_second(p, r) * (k-r)**q
               for r in range(1, min(p, k) + 1))


def orbital_chromatic(a: Sequence[int], pair: Edge, k: int) -> int:
    """Exact number of proper k-colorings of a single-pair orbital graph."""
    all_cycles = cycles(a)
    u, v = pair
    first = next(c for c in all_cycles if u in c)
    second = next(c for c in all_cycles if v in c)
    n = len(a)
    if first == second:
        length = len(first)
        step = (first.index(v) - first.index(u)) % length
        if step == 0:
            raise ValueError("The pair must be distinct.")
        components = gcd(length, step)
        size = length // components
        return k**(n-length) * ((k-1)**size + (-1)**size * (k-1))**components
    left, right = len(first), len(second)
    components = gcd(left, right)
    return k**(n-left-right) * bipartite_chromatic(
        left // components, right // components, k)**components


def accessible_and_distinguishable(a: Map, b: Map, tau: Map, initial: int = 0) -> bool:
    n = len(a)
    reached = {initial}
    queue = deque([initial])
    while queue:
        u = queue.popleft()
        for t in (a, b):
            if t[u] not in reached:
                reached.add(t[u]); queue.append(t[u])
    if len(reached) != n:
        return False
    for p in range(n):
        for q in range(p):
            seen = {(p, q)}
            todo = deque([(p, q)])
            distinguished = False
            while todo:
                x, y = todo.popleft()
                if tau[x] != tau[y]:
                    distinguished = True
                    break
                for t in (a, b):
                    pair = (t[x], t[y])
                    if pair not in seen:
                        seen.add(pair); todo.append(pair)
            if not distinguished:
                return False
    return True
