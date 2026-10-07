#!/usr/bin/env python3
"""Exhaustively audit the support bound for idempotents of the Brauer monoid.

Only Python's standard library is required.  The main test of idempotence uses
literal diagram multiplication in a graph with three rows of vertices.  The
support bound and the proposed equality characterization are tested separately.
An additional independent graph predicate audits the full classification by
alternating cap components.

Run:
    python3 code/brauer_audit.py --max-n 7 --output reproduced/brauer_audit.json

No optimization assumptions or sampling enter the certificate: every perfect
matching of 2*n ports is examined, including non-idempotents.  The default range
contains 146600 diagrams in total.  All checks raise explicit exceptions rather
than relying on ``assert``, so ``python -O`` does not disable them.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from math import factorial
from pathlib import Path
from typing import Iterator, Sequence


class AuditFailure(RuntimeError):
    """A mathematical or enumeration claim failed its exact check."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditFailure(message)


def perfect_matchings(n: int) -> Iterator[tuple[int, ...]]:
    """Yield all matchings of top 0..n-1 and bottom n..2*n-1 exactly once."""
    mate = [-1] * (2 * n)

    def extend(available: tuple[int, ...]) -> Iterator[tuple[int, ...]]:
        if not available:
            yield tuple(mate)
            return
        a = available[0]
        for k in range(1, len(available)):
            b = available[k]
            mate[a] = b
            mate[b] = a
            yield from extend(available[1:k] + available[k + 1 :])
            mate[a] = -1
            mate[b] = -1

    yield from extend(tuple(range(2 * n)))


def multiply(a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
    """Stack diagram a above b and discard all closed middle components."""
    require(len(a) == len(b) and len(a) % 2 == 0, "Invalid product sizes")
    n = len(a) // 2
    parent = list(range(3 * n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def join(x: int, y: int) -> None:
        parent[find(x)] = find(y)

    for i, j in enumerate(a):
        if i < j:
            join(i, j)
    for i, j in enumerate(b):
        if i < j:
            join(n + i, n + j)

    boundary_components: dict[int, list[int]] = {}
    for vertex in list(range(n)) + list(range(2 * n, 3 * n)):
        boundary_components.setdefault(find(vertex), []).append(vertex)
    result = [-1] * (2 * n)
    for component in boundary_components.values():
        require(len(component) == 2, f"Product has bad boundary: {component}")
        x, y = component
        x = x if x < n else x - n
        y = y if y < n else y - n
        result[x] = y
        result[y] = x
    require(all(v >= 0 for v in result), "Product left an unmatched boundary")
    return tuple(result)


def cap_components(mate: Sequence[int]) -> list[list[int]]:
    """Components on labels [n] using top caps and bottom caps as edges."""
    n = len(mate) // 2
    adjacency: list[list[int]] = [[] for _ in range(n)]
    for i in range(n):
        if mate[i] < n:
            adjacency[i].append(mate[i])
        if mate[n + i] >= n:
            adjacency[i].append(mate[n + i] - n)
    unseen = set(range(n))
    components = []
    while unseen:
        initial = min(unseen)
        unseen.remove(initial)
        component, stack = [], [initial]
        while stack:
            v = stack.pop()
            component.append(v)
            for w in adjacency[v]:
                if w in unseen:
                    unseen.remove(w)
                    stack.append(w)
        components.append(sorted(component))
    return components


def component_classification(
    mate: Sequence[int], components: Sequence[Sequence[int]]
) -> tuple[Counter[int], Counter[int]] | None:
    """Return path/cycle order counts if all through edges close internally.

    This predicate never multiplies diagrams.  A path component must have a
    single top-through endpoint a and bottom-through endpoint b, paired by the
    original diagram.  A cycle has neither endpoint.  Parallel top/bottom edges
    give a legitimate alternating cycle of order two.
    """
    n = len(mate) // 2
    paths: Counter[int] = Counter()
    cycles: Counter[int] = Counter()
    for component in components:
        a = [v for v in component if mate[v] >= n]
        b = [v for v in component if mate[n + v] < n]
        order = len(component)
        if not a and not b:
            if order < 2 or order % 2:
                return None
            cycles[order] += 1
        elif len(a) == len(b) == 1:
            if order % 2 == 0 or mate[a[0]] != n + b[0]:
                return None
            paths[order] += 1
        else:
            return None
    return paths, cycles


def triple_normal_form(
    mate: Sequence[int], components: Sequence[Sequence[int]]
) -> bool:
    """Independently check disjoint oriented three-point blocks and fixed points.

    On a three-point block (a,b,c), require exactly:
        top a -- bottom b, top b -- top c, bottom a -- bottom c,
    where a,b,c are distinct.  No reference to support, rank, or e^2 is made.
    """
    n = len(mate) // 2
    for component in components:
        if len(component) == 1:
            v = component[0]
            if mate[v] != n + v:
                return False
            continue
        if len(component) != 3:
            return False
        valid = False
        for a in component:
            for b in component:
                if a == b:
                    continue
                c = next(v for v in component if v != a and v != b)
                if (
                    mate[a] == n + b
                    and mate[b] == c
                    and mate[n + a] == n + c
                ):
                    valid = True
        if not valid:
            return False
    return True


def matching_of_permutation(p: Sequence[int]) -> tuple[int, ...]:
    n = len(p)
    result = [-1] * (2 * n)
    for i, j in enumerate(p):
        result[i] = n + j
        result[n + j] = i
    return tuple(result)


def self_check_multiplication() -> None:
    identity = matching_of_permutation((0, 1))
    swap = matching_of_permutation((1, 0))
    cap_cup = (1, 0, 3, 2)
    for diagram in (identity, swap, cap_cup):
        require(multiply(identity, diagram) == diagram, "Left unit check failed")
        require(multiply(diagram, identity) == diagram, "Right unit check failed")
    require(multiply(swap, swap) == identity, "Transposition square check failed")
    require(multiply(cap_cup, cap_cup) == cap_cup, "Cap-cup square check failed")
    p, q = (1, 2, 0), (1, 0, 2)
    expected = matching_of_permutation(tuple(q[p[i]] for i in range(3)))
    require(
        multiply(matching_of_permutation(p), matching_of_permutation(q)) == expected,
        "Noncommutative permutation product check failed",
    )


def audit_order(n: int) -> dict[str, object]:
    total = 0
    by_rank: Counter[int] = Counter()
    equality_by_rank: Counter[int] = Counter()
    by_deficit: Counter[int] = Counter()
    maximum_support_by_rank: dict[int, int] = {}
    for mate in perfect_matchings(n):
        total += 1
        idempotent = multiply(mate, mate) == mate
        components = cap_components(mate)
        classified = component_classification(mate, components)
        normal_form = triple_normal_form(mate, components)
        require(
            (classified is not None) == idempotent,
            f"Component classification failed at n={n}, mate={mate}",
        )
        if not idempotent:
            require(not normal_form, f"Non-idempotent normal form: {mate}")
            continue

        rank = sum(mate[i] >= n for i in range(n))
        corank = n - rank
        support = sum(mate[i] != n + i for i in range(n))
        require(corank % 2 == 0, f"Odd Brauer corank: {mate}")
        deficit = 3 * corank // 2 - support
        require(deficit >= 0, f"Support bound failed at n={n}, mate={mate}")
        require(
            (deficit == 0) == normal_form,
            f"Equality characterization failed at n={n}, mate={mate}",
        )
        if classified is None:
            raise AuditFailure("Idempotent was not classified")
        paths, cycles = classified
        predicted_deficit = sum(
            ((order - 1) // 2 - 1) * count
            for order, count in paths.items()
            if order > 1
        ) + sum((order // 2) * count for order, count in cycles.items())
        require(
            deficit == predicted_deficit,
            f"Exact component-deficit identity failed: {mate}",
        )
        bad_labels = sum(
            order * count for order, count in paths.items() if order > 3
        ) + sum(order * count for order, count in cycles.items())
        require(
            bad_labels <= 5 * deficit,
            f"Five-times-deficit stability bound failed: {mate}",
        )
        bad_corank = sum(
            (order - 1) * count for order, count in paths.items() if order > 3
        ) + sum(order * count for order, count in cycles.items())
        require(
            bad_corank <= 4 * deficit,
            f"Four-times-deficit corank bound failed: {mate}",
        )
        by_rank[rank] += 1
        by_deficit[deficit] += 1
        maximum_support_by_rank[rank] = max(
            maximum_support_by_rank.get(rank, 0), support
        )
        if deficit == 0:
            equality_by_rank[rank] += 1

    expected_total = factorial(2 * n) // (2**n * factorial(n))
    require(total == expected_total, f"Enumeration total failed at n={n}")
    expected_equality = {
        n - 2 * k: factorial(n) // (factorial(n - 3 * k) * factorial(k))
        for k in range(n // 3 + 1)
    }
    require(
        dict(equality_by_rank) == expected_equality,
        f"Equality count formula failed at n={n}: {dict(equality_by_rank)}",
    )
    expected_maximum_support = {
        rank: min(n, 3 * ((n - rank) // 2)) for rank in range(n, -1, -2)
    }
    require(
        maximum_support_by_rank == expected_maximum_support,
        f"Exact maximum-support formula failed at n={n}",
    )
    return {
        "n": n,
        "diagrams": total,
        "idempotents": sum(by_rank.values()),
        "idempotents_by_rank": dict(sorted(by_rank.items())),
        "equality_cases": sum(equality_by_rank.values()),
        "equality_cases_by_rank": dict(sorted(equality_by_rank.items())),
        "idempotents_by_deficit": dict(sorted(by_deficit.items())),
        "maximum_support_by_rank": dict(sorted(maximum_support_by_rank.items())),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=7)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    require(args.max_n >= 0, "--max-n must be nonnegative")
    self_check_multiplication()
    rows = []
    for n in range(args.max_n + 1):
        row = audit_order(n)
        rows.append(row)
        print(
            f"n={n}: {row['diagrams']} diagrams; "
            f"{row['idempotents']} idempotents; "
            f"{row['equality_cases']} equality cases; all checks passed",
            flush=True,
        )
    certificate = {
        "status": "pass",
        "method": "exhaustive perfect-matchings enumeration and explicit diagram squares",
        "maximum_n": args.max_n,
        "total_diagrams": sum(int(row["diagrams"]) for row in rows),
        "claims_checked": [
            "support(e) <= 3*(n-rank(e))/2 for every idempotent",
            "equality iff disjoint oriented three-point blocks and fixed points",
            "full idempotent classification by alternating cap components",
            "exact deficit identity in terms of path and cycle orders",
            "maximum support at fixed rank is min(n,3*(n-rank)/2)",
            "at most 5*deficit labels lie outside fixed points and triple blocks",
            "bad components contribute at most 4*deficit corank",
            "equality count at rank n-2*k is n!/((n-3*k)!*k!)",
        ],
        "orders": rows,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
        print(f"Certificate written to {args.output}", flush=True)


if __name__ == "__main__":
    main()
