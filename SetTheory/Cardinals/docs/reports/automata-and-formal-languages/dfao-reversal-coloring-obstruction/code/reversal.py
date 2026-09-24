#!/usr/bin/env python3
"""Exact tools accompanying the binary-DFAO reversal research note.

Python 3.9+; standard library only. Transformations are tuples t with
(t(q)) == t[q]. Function composition uses its usual right-to-left convention.
The coloring action is c -> c o t. No floating-point arithmetic is used.
"""
from collections import Counter, deque
from functools import lru_cache
from itertools import product
from math import factorial, gcd
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

Transformation = Tuple[int, ...]
Coloring = Tuple[int, ...]


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def validate_transform(t: Sequence[int], n: int) -> None:
    if len(t) != n or any(not isinstance(x, int) or not 0 <= x < n for x in t):
        raise ValueError("A transformation must map every state into range(n).")


def compose(a: Transformation, b: Transformation) -> Transformation:
    """Return a o b, not b o a."""
    return tuple(a[bq] for bq in b)


def act(c: Coloring, t: Transformation) -> Coloring:
    return tuple(c[tq] for tq in t)


def is_permutation(t: Transformation) -> bool:
    return len(set(t)) == len(t)


def first_collision(t: Transformation) -> Tuple[int, int]:
    previous: Dict[int, int] = {}
    for q, image in enumerate(t):
        if image in previous:
            return previous[image], q
        previous[image] = q
    raise ValueError("A permutation has no collision pair.")


def cycles(p: Transformation) -> List[Tuple[int, ...]]:
    if not is_permutation(p):
        raise ValueError("Cycle decomposition requires a permutation.")
    unseen = set(range(len(p)))
    answer = []
    while unseen:
        q = min(unseen)
        cycle = []
        while q in unseen:
            unseen.remove(q)
            cycle.append(q)
            q = p[q]
        answer.append(tuple(cycle))
    return answer


def permutation_order(p: Transformation) -> int:
    result = 1
    for cycle in cycles(p):
        result = lcm(result, len(cycle))
    return result


def collision_graph(p: Transformation, pair: Tuple[int, int]) -> Set[Tuple[int, int]]:
    """All unordered p-translates of one collision pair."""
    x, y = pair
    edges: Set[Tuple[int, int]] = set()
    while tuple(sorted((x, y))) not in edges:
        edges.add(tuple(sorted((x, y))))
        x, y = p[x], p[y]
    return edges


def proper(c: Coloring, edges: Iterable[Tuple[int, int]]) -> bool:
    return all(c[x] != c[y] for x, y in edges)


def surjective_proper_coloring(n: int, k: int,
                               edges: Iterable[Tuple[int, int]]) -> Coloring:
    """Color the graphs used in the proof, then split classes to use k colors.

    Supported graphs are bipartite graphs or graphs of maximum degree <= 2.
    This includes every orbit-of-an-edge graph and every graph of <= 2 edges.
    """
    if not 3 <= k <= n:
        raise ValueError("Require 3 <= k <= n.")
    edges = set(edges)
    adjacent = [set() for _ in range(n)]
    for x, y in edges:
        if x == y or not (0 <= x < n and 0 <= y < n):
            raise ValueError("Graph must be simple on range(n).")
        adjacent[x].add(y)
        adjacent[y].add(x)
    c = [-1] * n
    if max(map(len, adjacent), default=0) <= 2:
        # A greedy coloring uses at most degree + 1 colors.
        for q in range(n):
            used = {c[r] for r in adjacent[q] if c[r] >= 0}
            c[q] = next(i for i in range(3) if i not in used)
    else:
        for root in range(n):
            if c[root] >= 0:
                continue
            c[root] = 0
            queue = deque([root])
            while queue:
                q = queue.popleft()
                for r in adjacent[q]:
                    if c[r] == -1:
                        c[r] = 1 - c[q]
                        queue.append(r)
                    elif c[r] == c[q]:
                        raise ValueError("Graph is neither degree <= 2 nor bipartite.")
    labels = {color: i for i, color in enumerate(sorted(set(c)))}
    c = [labels[color] for color in c]
    counts = Counter(c)
    for new_color in range(len(counts), k):
        q = next(q for q in range(n) if counts[c[q]] > 1)
        counts[c[q]] -= 1
        c[q] = new_color
        counts[new_color] = 1
    answer = tuple(c)
    assert set(answer) == set(range(k)) and proper(answer, edges)
    return answer


def relabel_swap(c: Coloring, x: int, y: int) -> Coloring:
    return tuple(y if v == x else x if v == y else v for v in c)


def cyclic_membership(tau: Coloring, p: Transformation,
                      target: Coloring) -> Dict:
    """Decide target = tau o p^j without enumerating ord(p).

    Each p-cycle supplies one congruence for j. Failure is witnessed by a
    nonrotation, or by incompatible congruences. Time O(n^2) apart from
    polynomial-size integer arithmetic; exact generalized CRT.
    """
    n = len(p)
    validate_transform(p, n)
    if len(tau) != n or len(target) != n:
        raise ValueError("Colorings must have length n.")
    residue, modulus = 0, 1
    constraints = []
    for cycle in cycles(p):
        m = len(cycle)
        u = tuple(tau[q] for q in cycle)
        v = tuple(target[q] for q in cycle)
        shifts = [j for j in range(m)
                  if all(v[i] == u[(i + j) % m] for i in range(m))]
        if not shifts:
            return {"member": False, "reason": "nonrotation", "cycle": cycle,
                    "source": u, "target": v, "constraints": constraints}
        period = next(j for j in range(1, m + 1)
                      if all(u[i] == u[(i + j) % m] for i in range(m)))
        r = shifts[0] % period
        assert set(shifts) == {j for j in range(m) if j % period == r}
        item = {"cycle": cycle, "residue": r, "modulus": period}
        constraints.append(item)
        g = gcd(modulus, period)
        if (r - residue) % g:
            return {"member": False, "reason": "incompatible_congruences",
                    "accumulated_residue": residue, "accumulated_modulus": modulus,
                    "new_residue": r, "new_modulus": period,
                    "gcd": g, "constraints": constraints}
        reduced = period // g
        multiplier = (0 if reduced == 1 else
                      ((r - residue) // g * pow(modulus // g, -1, reduced)) % reduced)
        residue += modulus * multiplier
        modulus *= reduced
        residue %= modulus
    return {"member": True, "exponent": residue, "period": modulus,
            "constraints": constraints}


def missing_coloring(a: Transformation, b: Transformation,
                     tau: Coloring, k: int) -> Dict:
    """Construct a certificate of one coloring not in tau <a,b>."""
    n = len(tau)
    if not 3 <= k <= n or any(not 0 <= v < k for v in tau):
        raise ValueError("Require 3 <= k <= n and output labels in range(k).")
    validate_transform(a, n)
    validate_transform(b, n)
    missing = set(range(k)) - set(tau)
    if missing:
        return {"case": "missing_output", "target": (min(missing),) * n}
    pa, pb = is_permutation(a), is_permutation(b)
    if pa and pb:
        return {"case": "two_permutations", "target": (0,) * n}
    if not pa and not pb:
        pair_a, pair_b = first_collision(a), first_collision(b)
        edges = {tuple(sorted(pair_a)), tuple(sorted(pair_b))}
        c = surjective_proper_coloring(n, k, edges)
        if c == tau:
            c = relabel_swap(c, 0, 1)
        assert c != tau
        return {"case": "two_singular", "target": c,
                "collision_a": pair_a, "collision_b": pair_b,
                "edges": sorted(edges)}
    p, s = (a, b) if pa else (b, a)
    pair = first_collision(s)
    edges = collision_graph(p, pair)
    c = surjective_proper_coloring(n, k, edges)
    candidates = [c, relabel_swap(c, 0, 1), relabel_swap(c, 1, 2)]
    tests = []
    for candidate in candidates:
        result = cyclic_membership(tau, p, candidate)
        tests.append({"coloring": candidate, "result": result})
        if not result["member"]:
            return {"case": "mixed", "target": candidate,
                    "permutation": p, "singular": s, "collision": pair,
                    "edges": sorted(edges), "candidate_tests": tests}
    raise AssertionError("The noncommuting-relabellings lemma was violated.")


def orbit(tau: Coloring, generators: Sequence[Transformation]) -> Set[Coloring]:
    """Literal breadth-first search, for independent finite validation."""
    reached = {tau}
    queue = deque([tau])
    while queue:
        c = queue.popleft()
        for t in generators:
            d = act(c, t)
            if d not in reached:
                reached.add(d)
                queue.append(d)
    return reached


def accessible(n: int, generators: Sequence[Transformation], start: int = 0) -> bool:
    seen = {start}
    queue = deque([start])
    while queue:
        q = queue.popleft()
        for t in generators:
            r = t[q]
            if r not in seen:
                seen.add(r)
                queue.append(r)
    return len(seen) == n


def minimal_state_count(tau: Coloring,
                        generators: Sequence[Transformation]) -> int:
    """Moore refinement of all supplied states (check accessibility separately)."""
    partition = tau
    while True:
        signatures = [(partition[q],) + tuple(partition[t[q]] for t in generators)
                      for q in range(len(tau))]
        labels: Dict[Tuple[int, ...], int] = {}
        refined = tuple(labels.setdefault(sig, len(labels)) for sig in signatures)
        if len(set(refined)) == len(set(partition)):
            return len(set(refined))
        partition = refined


@lru_cache(maxsize=None)
def stirling(n: int, j: int) -> int:
    if n == j == 0:
        return 1
    if n == 0 or j == 0 or j > n:
        return 0
    return stirling(n - 1, j - 1) + j * stirling(n - 1, j)


@lru_cache(maxsize=None)
def bipartite_colorings(u: int, v: int, k: int) -> int:
    """Chromatic polynomial of K_{u,v} evaluated at k."""
    return sum(factorial(k) // factorial(k - i) * stirling(u, i) * (k - i) ** v
               for i in range(1, min(u, k) + 1))


@lru_cache(maxsize=None)
def permutation_orders(n: int, least: int = 1) -> frozenset:
    """Enumerate cycle-length partitions, retaining only possible orders."""
    if n == 0:
        return frozenset([1])
    return frozenset(lcm(i, order) for i in range(least, n + 1)
                     for order in permutation_orders(n - i, i))


@lru_cache(maxsize=None)
def H(r: int, t: int) -> int:
    return max(lcm(t, order) for order in permutation_orders(r))


def landau(k: int) -> int:
    return max(permutation_orders(k))


def structural_bound(n: int, k: int) -> Dict:
    """Universal upper bound, using all possible collision-orbit graph types.

    Bound includes nonsurjective tau as a separate case. Each candidate gap
    is proved in the article, and the smallest is the guaranteed gap.
    """
    if not 3 <= k <= n:
        raise ValueError("Require 3 <= k <= n.")
    q, z = divmod(n, k)
    balanced = factorial(n) // (factorial(q) ** (k - z) * factorial(q + 1) ** z)
    candidates = [
        {"gap": k ** n - (k - 1) ** n, "case": "nonsurjective"},
        {"gap": k ** n - balanced, "case": "two_permutations"},
        {"gap": (k - 1) ** 2 * k ** (n - 2) - 1, "case": "two_singular"}]
    for m in range(2, n + 1):
        r = n - m
        for d in range(1, m):
            if m % d:
                continue
            length = m // d
            number = ((k - 1) ** length + (-1) ** length * (k - 1)) ** d * k ** r
            period = H(r, m)
            candidates.append({"gap": number - period, "case": "cycle",
                               "m": m, "d": d, "isolated": r,
                               "proper_colorings": number, "period_bound": period})
    for a in range(1, n):
        for b in range(a, n - a + 1):
            r, d = n - a - b, gcd(a, b)
            number = bipartite_colorings(a // d, b // d, k) ** d * k ** r
            period = (max(H(r, a), H(r, b)) if k == 3 and d == 1
                      else H(r, lcm(a, b)))
            candidates.append({"gap": number - period, "case": "bipartite",
                               "a": a, "b": b, "d": d, "isolated": r,
                               "proper_colorings": number, "period_bound": period})
    best = min(candidates, key=lambda item: item["gap"])
    return {"n": n, "k": k, "upper_bound": k ** n - best["gap"],
            "gap": best["gap"], "minimizer": best,
            "candidates_examined": len(candidates)}


def davies_lower_bound(n: int, k: int) -> Optional[Dict]:
    """The published coprime-block lower bound, evaluated exactly.

    Its stated range is 2 <= k < n. This implementation uses k >= 3.
    """
    if not 3 <= k < n:
        return None
    candidates = []
    for ell in range(2, (n - 1) // 2 + 1):
        m = n - ell
        if gcd(ell, m) != 1:
            continue
        period = m if k == 3 else ell * m
        lower = k ** n - bipartite_colorings(ell, m, k) + period
        candidates.append({"lower_bound": lower, "ell": ell, "m": m,
                           "proper_colorings": bipartite_colorings(ell, m, k),
                           "period": period})
    return max(candidates, key=lambda x: x["lower_bound"]) if candidates else None


def u_witness(ell: int, m: int, k: int) -> Tuple[Transformation, Transformation, Coloring]:
    """The coprime two-cycle construction used for explicit finite checks.

    For k >= 3 the generator is the parity version described by Davies.
    The general lower theorem is a literature dependency, not inferred
    solely from these finite checks.
    """
    n = ell + m
    if not (1 < ell < m and gcd(ell, m) == 1 and 3 <= k < n):
        raise ValueError("Require 1 < ell < m, gcd=1, and 3 <= k < ell+m.")
    p = tuple(list(range(1, ell)) + [0] + list(range(ell + 1, n)) + [ell])
    s = list(range(n))
    s[0], s[n - 1] = ell, 0
    if ell % 2:
        s[1], s[2] = s[2], s[1]
    if k == 3:
        tau = (0,) * ell + (1,) + (2,) * (m - 1)
    else:
        left = min(k - 2, ell)
        right = k - left
        tau = tuple(list(range(left)) + [left - 1] * (ell - left)
                    + list(range(left, k)) + [k - 1] * (m - right))
    return p, tuple(s), tau


if __name__ == "__main__":
    import json
    p, s, tau = u_witness(3, 5, 5)
    print(json.dumps(missing_coloring(p, s, tau, 5), indent=2))
    print(json.dumps(structural_bound(8, 5), indent=2))
