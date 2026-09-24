#!/usr/bin/env python3
"""Exact finite checks for the preorder-polytope research manuscript.

Python 3.10+, standard library only. No network access or external data.
The proofs in article.tex, not these finite computations, establish the theorems.
Run: python3 code/verify.py --max-n 4 --out data/verification.json
"""
from __future__ import annotations
import argparse
import json
import math
import random
import time
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Iterator, Sequence

Vector = tuple[int, ...]
Relation = tuple[int, ...]  # row i is a bit mask of elements above i


def choose(z: int, k: int) -> int:
    """Polynomial binomial coefficient, including negative upper arguments."""
    if k < 0:
        return 0
    ans = 1
    for j in range(k):
        ans = ans * (z - j) // (j + 1)
    return ans


@lru_cache(maxsize=None)
def compositions_leq(n: int, total: int) -> tuple[Vector, ...]:
    if total < 0:
        return ()
    if n == 0:
        return ((),)
    return tuple((a,) + tail for a in range(total + 1)
                 for tail in compositions_leq(n - 1, total - a))


def preorders(n: int) -> Iterator[Relation]:
    """Exhaust every reflexive relation, retaining precisely the transitive ones."""
    if n < 0 or n > 5:
        raise ValueError("Exhaustive enumeration supports 0 <= n <= 5.")
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    for mask in range(1 << len(pairs)):
        rows = [1 << i for i in range(n)]
        for bit, (i, j) in enumerate(pairs):
            if mask >> bit & 1:
                rows[i] |= 1 << j
        if all(not (rows[i] >> j & 1) or rows[j] & ~rows[i] == 0
               for i in range(n) for j in range(n)):
            yield tuple(rows)


def dual(rows: Relation) -> Relation:
    n = len(rows)
    return tuple(sum(((rows[j] >> i) & 1) << j for j in range(n))
                 for i in range(n))


@lru_cache(maxsize=None)
def ideals(rows: Relation) -> tuple[Vector, ...]:
    """All nonempty order ideals as tuples of coordinate indices."""
    n = len(rows)
    down = dual(rows)
    return tuple(tuple(i for i in range(n) if mask >> i & 1)
                 for mask in range(1, 1 << n)
                 if all(not (mask >> i & 1) or down[i] & ~mask == 0
                        for i in range(n)))


def lattice_points(rows: Relation, b: Sequence[int], s: int = 0,
                   *, strict: bool = False) -> list[Vector]:
    """Enumerate from inequalities, independently of Postnikov's formula."""
    if len(b) != len(rows) or any(v < 0 for v in b) or s < 0:
        raise ValueError("Nonnegative capacities of the correct dimension required.")
    constraints = [(I, sum(b[i] for i in I) + s) for I in ideals(rows)]
    out = []
    for x in compositions_leq(len(rows), sum(b) + s):
        if strict:
            if any(v == 0 for v in x):
                continue
            good = all(sum(x[i] for i in I) < cap for I, cap in constraints)
        else:
            good = all(sum(x[i] for i in I) <= cap for I, cap in constraints)
        if good:
            out.append(x)
    return out


def rising_formula(Pdual: Sequence[Vector], b: Sequence[int], s: int) -> int:
    """F_tau(b,s); negative parameters mean polynomial evaluations."""
    n = len(b)
    return sum(choose(s + n - sum(a), n - sum(a)) *
               math.prod(choose(bi + ai - 1, ai) for bi, ai in zip(b, a))
               for a in Pdual)


def falling_formula(Pdual: Sequence[Vector], b: Sequence[int], s: int) -> int:
    n = len(b)
    return sum(choose(s, n - sum(a)) *
               math.prod(choose(bi + 1, ai) for bi, ai in zip(b, a))
               for a in Pdual)


def colored_count(rows: Relation, p: Sequence[int], q: Sequence[int]) -> int:
    """C_tau(p,q) by aggregated arrays and stars-and-bars, not graph duality."""
    if len(q) != len(rows) or any(v < 0 for v in q):
        raise ValueError("Nonnegative multiplicities of the correct dimension required.")
    return sum(math.prod(choose(qi + ai - 1, ai) for qi, ai in zip(q, a))
               for a in lattice_points(rows, p))


def multichains(rows: Relation, k: int, ell: int) -> int:
    n = len(rows)
    if k < 0 or ell < 0:
        raise ValueError("Multichain parameters must be nonnegative.")
    return colored_count(rows, (ell,) * n, (k,) * n)


def newton_coefficients(values: dict[tuple[int, int], int], n: int
                        ) -> dict[tuple[int, int], int]:
    """Bivariate forward differences on a total-degree triangular grid."""
    return {(i, j): sum((-1) ** (i + j - a - b) * math.comb(i, a) *
                       math.comb(j, b) * values[a, b]
                       for a in range(i + 1) for b in range(j + 1))
            for i in range(n + 1) for j in range(n + 1 - i)}


def evaluate_newton(coeff: dict[tuple[int, int], int], u: int, v: int) -> int:
    return sum(c * choose(u, i) * choose(v, j) for (i, j), c in coeff.items())


def hstar_from_counts(counts: Sequence[int], n: int) -> list[int]:
    return [sum((-1) ** j * math.comb(n + 1, j) * counts[i - j]
                for j in range(i + 1)) for i in range(n + 1)]


def word_histogram(rows: Relation) -> list[int]:
    """Enumerate all words, testing the lower-ideal counts directly."""
    n = len(rows)
    hist = [0] * (n + 1)
    for w in product(range(n), repeat=n):
        c = Counter(w)
        if all(sum(c[i] for i in I) >= len(I) for I in ideals(rows)):
            d = sum(w[i] > w[i + 1] for i in range(n - 1))
            hist[n - 1 - d] += 1
    return hist


def check_equal(a: object, b: object, context: object) -> None:
    if a != b:
        raise AssertionError(f"Mismatch in {context!r}: {a!r} != {b!r}")


def run_checks(max_n: int, seed: int) -> dict:
    start = time.monotonic()
    rng = random.Random(seed)
    totals: Counter = Counter()
    by_size: dict[str, int] = {}
    for n in range(1, max_n + 1):
        count = 0
        grid = [(r, s) for r in range(n + 1) for s in range(n + 1 - r)]
        for rows in preorders(n):
            count += 1
            rd = dual(rows)
            P = lattice_points(rows, (1,) * n)
            Pd = lattice_points(rd, (1,) * n)
            bases = [a for a in P if sum(a) == n]
            actual_maxima = [a for a in P if not any(
                all(x <= y for x, y in zip(a, b)) and a != b for b in P)]
            check_equal(set(bases), set(actual_maxima), ("maximality", rows))
            totals["maximality_checks"] += 1
            values = {}
            for r, s in grid:
                direct = len(lattice_points(rows, (r,) * n, s))
                values[r, s] = direct
                check_equal(direct, rising_formula(Pd, (r,) * n, s), ("rising", rows, r, s))
                check_equal(direct, falling_formula(Pd, (r,) * n, s), ("falling", rows, r, s))
                totals["direct_grid_values"] += 1
            coeff = newton_coefficients(values, n)
            # The difference has degree <= n. This triangular grid is unisolvent.
            for r, s in grid:
                check_equal(evaluate_newton(coeff, -r - 1, -s - 1),
                            (-1) ** n * values[r, s], ("reciprocity", rows, r, s))
                totals["reciprocity_unisolvent_tests"] += 1
            for r, s in product((1, 2), repeat=2):
                interior = lattice_points(rows, (r,) * n, s, strict=True)
                translated = {tuple(xi - 1 for xi in x) for x in interior}
                lower = set(lattice_points(rows, (r - 1,) * n, s - 1))
                check_equal(translated, lower, ("translation", rows, r, s))
                totals["interior_set_bijection_checks"] += 1
            h = hstar_from_counts([values[m, 0] for m in range(n + 1)], n)
            check_equal(h, word_histogram(rows), ("hstar", rows))
            totals["hstar_word_checks"] += 1
            zminus1 = sum(math.prod(choose(ai - 3, ai) for ai in a) for a in P)
            check_equal(zminus1, (-1) ** n * len(bases), ("zeta_minus_one", rows))
            totals["zeta_minus_one_checks"] += 1
            for k, ell in product(range(4), repeat=2):
                check_equal(multichains(rows, k, ell), multichains(rd, ell, k),
                            ("matrix", rows, k, ell))
                totals["matrix_duality_checks"] += 1
            for _ in range(8):
                p = tuple(rng.randrange(4) for _ in range(n))
                q = tuple(rng.randrange(4) for _ in range(n))
                check_equal(colored_count(rows, p, q), colored_count(rd, q, p),
                            ("colored_duality", rows, p, q))
                totals["heterogeneous_duality_checks"] += 1
                b = tuple(rng.randrange(1, 4) for _ in range(n))
                s = rng.randrange(1, 4)
                direct = len(lattice_points(rows, b, s))
                check_equal(direct, rising_formula(Pd, b, s), ("weighted_rising", rows, b, s))
                check_equal(direct, falling_formula(Pd, b, s), ("weighted_falling", rows, b, s))
                check_equal(rising_formula(Pd, tuple(-x for x in b), -s),
                            (-1) ** n * len(lattice_points(rows, tuple(x - 1 for x in b), s - 1)),
                            ("weighted_reciprocity", rows, b, s))
                totals["heterogeneous_reciprocity_checks"] += 1
        by_size[str(n)] = count
        print(f"n={n}: {count} labeled preorders; all checks passed", flush=True)
    expected = {"1": 1, "2": 4, "3": 29, "4": 355, "5": 6942}
    for n, count in by_size.items():
        check_equal(count, expected[n], ("enumeration_crosscheck", n))
    return {"status": "PASS", "max_n": max_n, "seed": seed,
            "preorders_by_size": by_size, "total_preorders": sum(by_size.values()),
            "checks": dict(totals), "elapsed_seconds": round(time.monotonic() - start, 3),
            "arithmetic": "Exact Python integers; no floating-point decisions.",
            "scope": "Exhaustive relations through max_n; eight seeded heterogeneous cases per relation.",
            "caveat": "Finite checks supplement but do not replace the proofs."}


def example_data() -> dict:
    fork = (7, 2, 4)  # 1<2 and 1<3
    examples = {"singleton": (1,), "antichain_3": (1, 2, 4),
                "equivalence_block_3": (7, 7, 7), "chain_2": (3, 2),
                "fork_V": fork, "fork_Lambda": dual(fork),
                "five_element_mixed": (21, 26, 21, 8, 16)}
    out = {}
    for name, rows in examples.items():
        n = len(rows)
        P = lattice_points(rows, (1,) * n)
        Pd = lattice_points(dual(rows), (1,) * n)
        counts = [len(lattice_points(rows, (m,) * n)) for m in range(n + 1)]
        vals = {(r, s): len(lattice_points(rows, (r,) * n, s))
                for r in range(n + 1) for s in range(n + 1 - r)}
        coeff = newton_coefficients(vals, n)
        out[name] = {"relation_rows": list(rows), "nonempty_ideals": [list(I) for I in ideals(rows)],
                     "lattice_count": len(P), "maximal_count": sum(sum(a) == n for a in P),
                     "dual_maximal_count": sum(sum(a) == n for a in Pd),
                     "ehrhart_values_0_to_n": counts, "hstar": hstar_from_counts(counts, n),
                     "double_ehrhart_newton_coefficients": {f"{i},{j}": c for (i,j),c in coeff.items() if c},
                     "matrix_0_to_3": [[multichains(rows, k, ell) for ell in range(4)] for k in range(4)]}
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=4, choices=range(1, 6))
    parser.add_argument("--seed", type=int, default=20260919)
    parser.add_argument("--out", type=Path, default=Path("data/verification.json"))
    args = parser.parse_args()
    result = run_checks(args.max_n, args.seed)
    result["examples"] = example_data()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "examples"}, indent=2))


if __name__ == "__main__":
    main()
