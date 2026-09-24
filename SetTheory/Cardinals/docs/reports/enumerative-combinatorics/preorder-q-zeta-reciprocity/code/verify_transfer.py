#!/usr/bin/env python3
"""Exact independent checks for the transfer-involution proof (Proof B).

Originally shipped as code/verify.py of preorder-q-reciprocity-weighted;
renamed here so that the three verifiers of the merged package coexist.

Python 3.10+, standard library only. Run from anywhere:
    python code/verify_transfer.py --output data/verification_transfer.json
All integer polynomials are coefficient lists in ascending powers. No floating
point arithmetic, symbolic algebra package, or theorem-specific data is needed.
The finite checks supplement, and do not replace, the article's general proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import comb, prod
from pathlib import Path
import json
import random
from typing import Iterable, Iterator, Sequence

Vector = tuple[int, ...]
Relation = tuple[int, ...]  # row i is the bitset of j with i <= j
Poly = list[int]


def demand(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def trim(p: Poly) -> Poly:
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p or [0]


def add(p: Sequence[int], q: Sequence[int]) -> Poly:
    z = [0] * max(len(p), len(q))
    for i, v in enumerate(p): z[i] += v
    for i, v in enumerate(q): z[i] += v
    return trim(z)


def mul(p: Sequence[int], q: Sequence[int]) -> Poly:
    z = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q): z[i + j] += a * b
    return trim(z)


def eval_poly(p: Sequence[int], t: Fraction) -> Fraction:
    ans = Fraction(0)
    for c in reversed(p): ans = ans * t + c
    return ans


def pbinom(top: int, bottom: int) -> int:
    """Polynomial binomial coefficient, valid for negative top integers."""
    if bottom < 0: return 0
    return prod(top - j for j in range(bottom)) // prod(range(1, bottom + 1))


def transpose(up: Relation) -> Relation:
    n = len(up)
    return tuple(sum(1 << j for j in range(n) if up[j] >> i & 1)
                 for i in range(n))


def transitive_closure(n: int, edges: Iterable[tuple[int, int]]) -> Relation:
    rows = [1 << i for i in range(n)]
    for i, j in edges:
        if not (0 <= i < n and 0 <= j < n):
            raise ValueError("edge endpoint outside relation")
        rows[i] |= 1 << j
    for k in range(n):
        for i in range(n):
            if rows[i] >> k & 1: rows[i] |= rows[k]
    return tuple(rows)


def preorders(n: int) -> Iterator[Relation]:
    """Enumerate every reflexive transitive labelled relation, without quotienting."""
    off = [(i, j) for i in range(n) for j in range(n) if i != j]
    for mask in range(1 << len(off)):
        rows = [1 << i for i in range(n)]
        for k, (i, j) in enumerate(off):
            if mask >> k & 1: rows[i] |= 1 << j
        if all(not (rows[i] >> j & 1) or not (rows[j] & ~rows[i])
               for i in range(n) for j in range(n)):
            yield tuple(rows)


@lru_cache(None)
def ideals(up: Relation) -> tuple[tuple[int, ...], ...]:
    down = transpose(up)
    n = len(up)
    return tuple(tuple(i for i in range(n) if mask >> i & 1)
                 for mask in range(1, 1 << n)
                 if all(not (mask >> i & 1) or not (down[i] & ~mask)
                        for i in range(n)))


@lru_cache(None)
def weak_vectors(n: int, bound: int) -> tuple[Vector, ...]:
    """All nonnegative n-vectors with total at most bound."""
    if n == 0: return ((),)
    return tuple((a,) + tail for a in range(bound + 1)
                 for tail in weak_vectors(n - 1, bound - a))


def lattice_points(up: Relation, u: Sequence[int] | None = None,
                   v: int = 0) -> tuple[Vector, ...]:
    n = len(up)
    if u is None: u = (1,) * n
    if len(u) != n or min((*u, v), default=0) < 0:
        raise ValueError("lattice point enumeration requires nonnegative capacities")
    constraints = [(I, sum(u[i] for i in I) + v) for I in ideals(up)]
    return tuple(a for a in weak_vectors(n, sum(u) + v)
                 if all(sum(a[i] for i in I) <= cap for I, cap in constraints))


def allocation_bases(up: Relation) -> set[Vector]:
    """Independent enumeration: allocate source i's unit to an upper neighbour."""
    n = len(up)
    states = {(0,) * n}
    for row in up:
        out = set()
        for a in states:
            for j in range(n):
                if row >> j & 1:
                    b = list(a); b[j] += 1; out.add(tuple(b))
        states = out
    return states


def base_support(B: Sequence[Vector]) -> dict[int, int]:
    counts: Counter[int] = Counter()
    for b in B:
        counts[sum(1 << i for i, a in enumerate(b) if a)] += 1
    return dict(counts)


def ternary_support(P: Sequence[Vector], n: int) -> dict[int, int]:
    """Expand the left side of the full multivariate support identity."""
    ans: Counter[int] = Counter()
    for a in P:
        if max(a, default=0) > 2: continue
        local = {0: (-1) ** n}
        for i, k in enumerate(a):
            new: Counter[int] = Counter()
            for mask, c in local.items():
                if k == 0: new[mask] += c
                elif k == 1:
                    new[mask] -= c
                    new[mask | (1 << i)] -= c
                else: new[mask | (1 << i)] += c
            local = dict(new)
        ans.update(local)
    return {mask: c for mask, c in ans.items() if c}


def f_negative(r: int) -> list[Poly]:
    """Coefficients in z of product_{j=0}^r (1-t^j z)."""
    f = [[1]]
    for j in range(r + 1):
        out = [[0] for _ in range(len(f) + 1)]
        for a, p in enumerate(f):
            out[a] = add(out[a], p)
            out[a + 1] = add(out[a + 1], [0] * j + [-x for x in p])
        f = out
    return f


def c_positive(r: int, a: int) -> Poly:
    """Independent positive formula using subsets of colors and compositions."""
    if a == 0: return [1]
    p = [0] * (r * a + 1)
    for s in range(1, min(r, a) + 1):
        for colors in combinations(range(1, r + 1), s):
            p[sum(colors)] += comb(a - 1, s - 1)
    return trim(p)


def sum_local(points: Sequence[Vector], local: Sequence[Sequence[int]]) -> Poly:
    total = [0]
    for a in points:
        p = [1]
        for k in a:
            if k >= len(local): p = [0]; break
            p = mul(p, local[k])
        total = add(total, p)
    return total


def signed_negative(P: Sequence[Vector], n: int, r: int) -> Poly:
    return [(-1) ** n * a for a in sum_local(P, f_negative(r))]


def positive_negative(B: Sequence[Vector], n: int, r: int) -> Poly:
    return sum_local(B, [c_positive(r, a) for a in range(n + 1)])


def transform(f: Sequence[int], n: int) -> Poly:
    """First n+1 coefficients of (1-z) f(-z/(1-z))."""
    f = list(f) + [0] * max(0, n + 1 - len(f))
    out = [f[0]]
    if n: out.append(-f[0] - f[1])
    for a in range(2, n + 1):
        out.append(sum((-1) ** k * comb(a - 2, k - 2) * f[k]
                       for k in range(2, a + 1)))
    return out


def master_check(P: Sequence[Vector], B: Sequence[Vector], n: int,
                 rng: random.Random) -> None:
    fs = [[rng.randrange(-3, 4) for _ in range(n + 1)] for _ in range(n)]
    gs = [transform(f, n) for f in fs]
    lhs = sum(prod(fs[i][a[i]] for i in range(n)) for a in P)
    rhs = (-1) ** n * sum(prod(gs[i][b[i]] for i in range(n)) for b in B)
    demand(lhs == rhs, f"general coefficient transfer failed: {n}, {fs}")
    demand(all(transform(g, n) == f for f, g in zip(fs, gs)), "involution failed")


def ehrhart_formula(up: Relation, u: Sequence[int], v: int) -> int:
    n = len(up)
    return sum(pbinom(v + n - sum(a), n - sum(a)) *
               prod(pbinom(u[i] + a[i] - 1, a[i]) for i in range(n))
               for a in lattice_points(transpose(up)))


def q_integer(m: int, q: int) -> Fraction:
    return (Fraction(q) ** m - 1) / (q - 1)


def lagrange(xs: Sequence[Fraction], ys: Sequence[Fraction],
             target: Fraction) -> Fraction:
    ans = Fraction(0)
    for i, y in enumerate(ys):
        value = y
        for j, x in enumerate(xs):
            if i != j: value *= (target - x) / (xs[i] - x)
        ans += value
    return ans


def chain_interpolation(P: Sequence[Vector], B: Sequence[Vector],
                        n: int, q: int, max_r: int) -> int:
    """Build positive-m chains by DP, interpolate, and test negative inputs."""
    lowers = [[j for j, b in enumerate(P) if all(x <= y for x, y in zip(b, a))]
              for a in P]
    weights = [q ** sum(a) for a in P]
    values = weights[:]
    xs, ys = [], []
    for length in range(1, n + 2):
        xs.append(q_integer(length + 1, q))
        ys.append(Fraction(sum(values)))
        values = [weights[i] * sum(values[j] for j in lowers[i])
                  for i in range(len(P))]
    # A further positive node checks the degree-bound interpolation independently.
    extra_x = q_integer(n + 3, q)
    demand(lagrange(xs, ys, extra_x) == sum(values), "positive interpolation failed")
    for r in range(1, max_r + 1):
        actual = lagrange(xs, ys, q_integer(-r, q))
        expected = (-1) ** n * eval_poly(positive_negative(B, n, r), Fraction(1, q))
        demand(actual == expected, f"chain interpolation failed: n={n}, q={q}, r={r}")
    return max_r + 1


def max_classes(up: Relation) -> int:
    """Number of maximal equivalence classes of the quotient partial order."""
    down = transpose(up)
    return len({up[i] for i in range(len(up)) if up[i] == (up[i] & down[i])})


def check_relation(up: Relation, max_r: int, rng: random.Random) -> dict:
    n = len(up)
    P = lattice_points(up)
    B = tuple(a for a in P if sum(a) == n)
    demand(set(B) == allocation_bases(up), "independent base enumerations differ")
    # Check maximality directly, not just the claimed rank characterization.
    pset = set(P)
    max_actual = {a for a in P if not any(tuple(a[j] + (j == i) for j in range(n))
                                          in pset for i in range(n))}
    demand(set(B) == max_actual, "maximal-element rank characterization failed")
    demand(ternary_support(P, n) == base_support(B), "multivariate identity failed")
    master_check(P, B, n, rng)
    for r in range(1, max_r + 1):
        lhs = signed_negative(P, n, r)
        rhs = positive_negative(B, n, r)
        demand(lhs == rhs, f"negative polynomial identity failed: {up}, r={r}")
        demand(all(c >= 0 for c in rhs), "positivity failed")
        demand(len(rhs) == r * n + 1 and rhs[-1] == 1, "monic degree failed")
        low = next(i for i, c in enumerate(rhs) if c)
        demand(low == max_classes(up), "lowest degree / maximal-class formula failed")
    return {"relation_rows": list(up), "points": len(P), "bases": len(B),
            "support_polynomial": positive_negative(B, n, 1)}


def examples() -> dict[str, Relation]:
    return {
        "discrete_3": transitive_closure(3, []),
        "chain_3": transitive_closure(3, [(0, 1), (1, 2)]),
        "one_equivalence_class_3": transitive_closure(3, [(0, 1), (1, 2), (2, 0)]),
        "fork_3": transitive_closure(3, [(0, 1), (0, 2)]),
        "diamond_4": transitive_closure(4, [(0, 1), (0, 2), (1, 3), (2, 3)]),
        "source_running_5": transitive_closure(5, [(0, 2), (2, 0), (1, 3),
                                                  (1, 4), (0, 4)]),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=4, choices=range(0, 6),
                        help="exhaustive labelled preorders; 5 is substantially slower")
    parser.add_argument("--max-r", type=int, default=4, choices=range(1, 8))
    parser.add_argument("--output", type=Path, default=Path("data/verification_transfer.json"))
    args = parser.parse_args()
    rng = random.Random(20260920)
    counts = {}
    records = []
    interp_count = cap_count = 0
    for n in range(args.max_n + 1):
        count = 0
        for up in preorders(n):
            record = check_relation(up, args.max_r, rng)
            records.append(record); count += 1
            if n <= 3:
                P = lattice_points(up)
                B = tuple(a for a in P if sum(a) == n)
                for q in (2, 3):
                    interp_count += chain_interpolation(P, B, n, q, args.max_r)
                if n:
                    for u in product((1, 2), repeat=n):
                        for v in (0, 1, 2):
                            demand(ehrhart_formula(up, u, v) == len(lattice_points(up, u, v)),
                                   "capacity lattice count formula failed")
                            cap_count += 1
                        for v in (1, 2):
                            actual = ehrhart_formula(up, tuple(-a for a in u), -v)
                            expected = (-1) ** n * len(lattice_points(up, tuple(a - 1 for a in u), v - 1))
                            demand(actual == expected, "capacity reciprocity failed")
                            cap_count += 1
        counts[str(n)] = count
        print(f"All labelled preorders of size {n}: {count} passed.", flush=True)
    example_data = {}
    for name, up in examples().items():
        rec = check_relation(up, args.max_r, rng)
        P = lattice_points(up); B = tuple(a for a in P if sum(a) == len(up))
        for q in (2, 3):
            interp_count += chain_interpolation(P, B, len(up), q, args.max_r)
        rec["negative_evaluations"] = {str(r): positive_negative(B, len(up), r)
                                       for r in range(1, args.max_r + 1)}
        rec["bases_explicit"] = [list(b) for b in B]
        example_data[name] = rec
    random_checks = 0
    for n in (5, 6, 7, 8):
        for trial in range(6):
            # Cycles are allowed on two trials, testing genuine equivalence blocks.
            if trial < 2:
                edges = [(i, j) for i in range(n) for j in range(n) if i != j
                         and rng.random() < .12]
            else:
                edges = [(i, j) for i in range(n) for j in range(i + 1, n)
                         if rng.random() < .12 + .12 * trial]
            check_relation(transitive_closure(n, edges), args.max_r, rng)
            random_checks += 1
        print(f"Additional deterministic random preorders of size {n}: 6 passed.", flush=True)
    report = {
        "status": "PASS", "arithmetic": "exact integers and fractions; no floating point",
        "seed": 20260920, "exhaustive_labelled_preorders": counts,
        "exhaustive_total": sum(counts.values()),
        "negative_r_tested": list(range(1, args.max_r + 1)),
        "negative_polynomial_checks_exhaustive": sum(counts.values()) * args.max_r,
        "multivariate_support_checks_exhaustive": sum(counts.values()),
        "general_coefficient_transform_checks_exhaustive": sum(counts.values()),
        "capacity_checks": cap_count, "chain_interpolation_checks": interp_count,
        "additional_random_preorders": random_checks, "examples": example_data,
        "exhaustive_records": records,
        "limitations": "Finite checks are not a formal proof and do not establish novelty."
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"PASS. Results written to {args.output}", flush=True)


if __name__ == "__main__":
    main()
