#!/usr/bin/env python3
"""Exact checks for support-refined preorder reciprocity (Python 3.9+).
Exhaustive means all labelled reflexive transitive relations.
These tests complement, and do not replace, the proof in article.tex.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, platform, random, time
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Iterator, Sequence
Vector = tuple[int, ...]
Relation = tuple[int, ...]  # bit j of rows[i] means i <= j


def popcount(x: int) -> int:
    return bin(x).count("1")  # compatible with Python 3.9


@lru_cache(maxsize=None)
def subsets(n: int) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(i for i in range(n) if m >> i & 1) for m in range(1 << n))


@lru_cache(maxsize=None)
def sizes(n: int) -> tuple[int, ...]:
    return tuple(popcount(i) for i in range(1 << n))


@lru_cache(maxsize=None)
def compositions(total: int, n: int) -> tuple[Vector, ...]:
    if n == 0:
        return ((),) if total == 0 else ()
    if n == 1:
        return ((total,),)
    return tuple((first,) + tail for first in range(total + 1)
                 for tail in compositions(total - first, n - 1))


def transpose(rows: Relation) -> Relation:
    return tuple(sum(1 << j for j in range(len(rows)) if rows[j] >> i & 1)
                 for i in range(len(rows)))


def is_preorder(rows: Relation) -> bool:
    n = len(rows)
    if any(not rows[i] >> i & 1 for i in range(n)):
        return False
    idx = subsets(n)
    return all((rows[j] | row) == row for row in rows for j in idx[row])


def closure(rows: Relation) -> Relation:
    n = len(rows)
    r = [row | (1 << i) for i, row in enumerate(rows)]
    for k in range(n):
        for i in range(n):
            if r[i] >> k & 1:
                r[i] |= r[k]
    return tuple(r)


def all_preorders(n: int) -> Iterator[Relation]:
    if n == 0:
        yield ()
        return
    idx = subsets(n)
    choices = [tuple(m for m in range(1 << n) if m >> i & 1) for i in range(n)]
    for r in itertools.product(*choices):
        if all((r[j] | row) == row for row in r for j in idx[row]):
            yield r


def ideal_masks(rows: Relation) -> tuple[int, ...]:
    n = len(rows)
    down, idx = transpose(rows), subsets(n)
    return tuple(m for m in range(1, 1 << n)
                 if all((down[i] | m) == m for i in idx[m]))


def feasible(v: Vector, ideals: Sequence[int]) -> bool:
    idx, sz = subsets(len(v)), sizes(len(v))
    return all(sum(v[i] for i in idx[m]) <= sz[m] for m in ideals)


def lattice_points(rows: Relation) -> tuple[Vector, ...]:
    n, ideals = len(rows), ideal_masks(rows)
    return tuple(v for total in range(n + 1) for v in compositions(total, n)
                 if feasible(v, ideals))


def bases_from_ideals(rows: Relation) -> tuple[Vector, ...]:
    n, ideals = len(rows), ideal_masks(rows)
    return tuple(v for v in compositions(n, n) if feasible(v, ideals))


def bases_from_assignments(rows: Relation) -> set[Vector]:
    """Independent model: move each source to an allowed destination."""
    n, idx = len(rows), subsets(len(rows))
    result: set[Vector] = {(0,) * n}
    for row in rows:
        nxt: set[Vector] = set()
        for v in result:
            for j in idx[row]:
                w = list(v)
                w[j] += 1
                nxt.add(tuple(w))
        result = nxt
    return result


def support(v: Vector) -> int:
    return sum(1 << i for i, x in enumerate(v) if x)


def support_counts(bases: Iterable[Vector], n: int) -> list[int]:
    result = [0] * (1 << n)
    for a in bases:
        result[support(a)] += 1
    return result


def boolean_coefficients(rows: Relation) -> list[int]:
    """(-1)^n sum_{B,S, 1_B+1_S in P} (-1)^(|B|+|S|) z^B."""
    n, ideals, sz = len(rows), ideal_masks(rows), sizes(len(rows))
    parity = tuple((-1) ** k for k in sz)
    counts = [[sz[b & i] for b in range(1 << n)] for i in ideals]
    bounds, answer = [sz[i] for i in ideals], []
    for b in range(1 << n):
        residual = [bound - c[b] for c, bound in zip(counts, bounds)]
        total = 0
        for s in range(1 << n):
            if all(c[s] <= r for c, r in zip(counts, residual)):
                total += parity[s]
        answer.append((-1) ** (n + sz[b]) * total)
    return answer


def contained_counts(coeff: Sequence[int]) -> list[int]:
    """Boolean zeta transform: count supports contained in each mask."""
    result, n = list(coeff), (len(coeff) - 1).bit_length()
    for i in range(n):
        for mask in range(1 << n):
            if mask >> i & 1:
                result[mask] += result[mask ^ (1 << i)]
    return result


def interior_counts(rows: Relation) -> list[int]:
    """Strict inequalities of Q_{tau*}(1+1_T), without Postnikov."""
    n = len(rows)
    if n == 0:
        return [1]
    filters, idx, sz = ideal_masks(transpose(rows)), subsets(n), sizes(n)
    answer = [0] * (1 << n)
    candidates = [(sum(v), tuple(sum(v[i] for i in idx[f]) for f in filters))
                  for total in range(n) for v in compositions(total, n)]
    for t in range(1, 1 << n):
        cap = tuple(sz[t & f] - 1 for f in filters)
        if min(cap) < 0:
            continue
        answer[t] = sum(1 for total, sums in candidates if total < sz[t]
                        and all(a <= b for a, b in zip(sums, cap)))
    return answer


def rising_binomial(t: int, a: int) -> Fraction:
    value = Fraction(1)
    for k in range(a):
        value *= Fraction(t + k, k + 1)
    return value


def weighted_lattice_formula(rows: Relation, cap: Vector) -> Fraction:
    result = Fraction(0)
    for a in lattice_points(rows):
        term = Fraction(1)
        for t, k in zip(cap, a):
            term *= rising_binomial(t, k)
        result += term
    return result


def direct_weighted_lattice(rows: Relation, cap: Vector) -> int:
    ideals, idx = ideal_masks(rows), subsets(len(rows))
    bounds = [(idx[i], sum(cap[j] for j in idx[i])) for i in ideals]
    return sum(all(sum(v[j] for j in inds) <= bound for inds, bound in bounds)
               for total in range(sum(cap) + 1)
               for v in compositions(total, len(rows)))


def lagrange_at(nodes: Sequence[int], vals: Sequence[int], x: Fraction) -> Fraction:
    total = Fraction(0)
    for j, y in enumerate(vals):
        term = Fraction(y)
        for k, a in enumerate(nodes):
            if j != k:
                term *= (x - a) / (nodes[j] - a)
        total += term
    return total


def q_integer(m: int, q: int) -> int:
    return m if q == 1 else (q ** m - 1) // (q - 1)


def direct_qzeta_negative(rows: Relation, q: int) -> Fraction:
    """Positive multichains + interpolation, not the claimed negative formula."""
    if q < 1:
        raise ValueError("The test uses positive integer q.")
    n, pts = len(rows), lattice_points(rows)
    below = [tuple(i for i, a in enumerate(pts)
                   if all(x <= y for x, y in zip(a, b))) for b in pts]
    weights = [q ** sum(a) for a in pts]
    f, vals, nodes = weights[:], [], []
    for m in range(2, n + 3):
        nodes.append(q_integer(m, q))
        vals.append(sum(f))
        f = [w * sum(f[i] for i in inds) for w, inds in zip(weights, below)]
    return lagrange_at(nodes, vals, Fraction(-1, q))


def random_preorder(n: int, rng: random.Random, mode: int) -> Relation:
    # Sparse DAG, dense DAG, arbitrary directed closure, and block preorder.
    if mode % 4 in (0, 1):
        prob = 0.2 if mode % 4 == 0 else 0.65
        perm = list(range(n))
        rng.shuffle(perm)
        rows = [1 << i for i in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < prob:
                    rows[perm[i]] |= 1 << perm[j]
        return closure(tuple(rows))
    if mode % 4 == 2:
        p = 1.0 / max(2, n)
        return closure(tuple(sum(1 << j for j in range(n)
                                 if i == j or rng.random() < p) for i in range(n)))
    k = rng.randint(1, n)
    labels = list(range(k)) + [rng.randrange(k) for _ in range(n-k)]
    rng.shuffle(labels)
    order = closure(tuple((1 << i) | sum(1 << j for j in range(i + 1, k)
                                        if rng.random() < 0.35) for i in range(k)))
    return tuple(sum(1 << j for j in range(n) if order[labels[i]] >> labels[j] & 1)
                 for i in range(n))


def example_rows() -> dict[str, Relation]:
    source = closure((0b10101, 0b11010, 0b10101, 0b01000, 0b10000))
    return {
        "antichain_5": tuple(1 << i for i in range(5)),
        "chain_5": tuple(sum(1 << j for j in range(i, 5)) for i in range(5)),
        "one_equivalence_class_5": (31,) * 5,
        "source_example_5": source,
        "fork_3": closure((0b111, 0b010, 0b100)),
    }


def check_preorder(rows: Relation, geometry: bool = False) -> tuple[int, int]:
    if not is_preorder(rows):
        raise AssertionError(("not a preorder", rows))
    n, b = len(rows), bases_from_ideals(rows)
    expected, actual = support_counts(b, n), boolean_coefficients(rows)
    if actual != expected:
        raise AssertionError(("Boolean support failure", rows, actual, expected))
    if geometry:
        interior = interior_counts(rows)
        if interior != contained_counts(expected):
            raise AssertionError(("interior failure", rows, interior, expected))
        if set(b) != bases_from_assignments(rows):
            raise AssertionError(("assignment failure", rows))
    return len(b), 1 << n


def general_downset_counterexample() -> dict:
    neighborhoods = (0b011, 0b110, 0b101)
    b, p = bases_from_assignments(neighborhoods), set()
    for a in b:
        p.update(itertools.product(*(range(x+1) for x in a)))
    coeff = [0] * 8
    for left in range(8):
        for right in range(8):
            c = tuple(((left >> i) & 1) + ((right >> i) & 1) for i in range(3))
            if c in p:
                coeff[left] += (-1) ** (3 + popcount(left) + popcount(right))
    true = support_counts(b, 3)
    assert coeff == [0, 1, 1, 2, 1, 2, 2, 1]
    assert true == [0, 0, 0, 2, 0, 2, 2, 1]
    return {"rows": neighborhoods, "bases": sorted(b),
            "signed_boolean_support_coefficients": coeff,
            "actual_support_coefficients": true}


def run(max_n: int, random_count: int, seed: int) -> dict:
    started = time.time()
    report = {"status": "PASS", "python": platform.python_version(),
              "seed": seed, "exhaustive": [], "random": [], "examples": {},
              "scope": "Exact finite tests; not proof-assistant verification."}
    witness_hash = hashlib.sha256()
    for n in range(max_n + 1):
        start, count, support_total, bases_total = time.time(), 0, 0, 0
        for rows in all_preorders(n):
            base_count, masks = check_preorder(rows, geometry=True)
            count += 1
            support_total += masks
            bases_total += base_count
            witness_hash.update((str(rows) + ":" + str(base_count) + "\n").encode())
        row = {"n": n, "labelled_preorders": count,
               "support_coefficients_checked": support_total,
               "interior_capacities_checked": support_total,
               "assignment_models_checked": count, "maximal_points_total": bases_total,
               "seconds": round(time.time()-start, 3)}
        report["exhaustive"].append(row)
        print("Exhaustive:", row, flush=True)
    rng = random.Random(seed)
    for n in range(max_n + 1, max_n + 4):
        start, tested = time.time(), []
        for k in range(random_count):
            rows = random_preorder(n, rng, k)
            check_preorder(rows, geometry=(n <= 7))
            tested.append(rows)
        row = {"n": n, "cases": random_count, "distinct_relations": len(set(tested)),
               "rows": tested, "support_coefficients_checked": random_count*(1<<n),
               "geometry_checked": n <= 7, "seconds": round(time.time()-start, 3)}
        report["random"].append(row)
        print("Random:", {k:v for k,v in row.items() if k != "rows"}, flush=True)
    interpolation_checks = capacity_checks = 0
    for name, rows in example_rows().items():
        n = len(rows)
        coeff = support_counts(bases_from_ideals(rows), n)
        card = [sum(c for mask,c in enumerate(coeff) if popcount(mask) == k)
                for k in range(n+1)]
        vals = {}
        for q in (1, 2, 3, 5):
            actual = direct_qzeta_negative(rows, q)
            expected = (-1) ** n * sum(Fraction(c, q**k) for k,c in enumerate(card))
            assert actual == expected, (name, q, actual, expected)
            vals[str(q)] = str(actual)
            interpolation_checks += 1
        caps = [(0,)*n, (1,)*n, tuple(1+(i%2) for i in range(n)),
                tuple(2 if i == 0 else 0 for i in range(n))]
        for cap in caps:
            a = weighted_lattice_formula(rows, cap)
            b = direct_weighted_lattice(transpose(rows), cap)
            assert a == b, (name, cap, a, b)
            capacity_checks += 1
        for t in range(1<<n):
            cap = tuple(-1-((t>>i)&1) for i in range(n))
            a = weighted_lattice_formula(rows, cap)
            assert a == (-1)**n * contained_counts(coeff)[t]
            capacity_checks += 1
        report["examples"][name] = {"rows": rows, "support_counts": coeff,
                                    "support_size_counts": card,
                                    "qzeta_from_positive_multichains": vals}
        print("Example:", name, card, vals, flush=True)
    report["positive_multichain_interpolations"] = interpolation_checks
    report["weighted_polynomial_evaluations"] = capacity_checks
    report["counterexample_outside_preorders"] = general_downset_counterexample()
    report["exhaustive_witness_stream_sha256"] = witness_hash.hexdigest()
    report["elapsed_seconds"] = round(time.time()-started, 3)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive", type=int, default=5, choices=range(0, 6))
    parser.add_argument("--random-per-size", type=int, default=16)
    parser.add_argument("--seed", type=int, default=20260920)
    parser.add_argument("--output", type=Path, default=Path("data/verification.json"))
    args = parser.parse_args()
    if args.random_per_size < 0:
        parser.error("--random-per-size must be nonnegative")
    report = run(args.exhaustive, args.random_per_size, args.seed)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("PASS; report:", args.output, "elapsed:", report["elapsed_seconds"], flush=True)


if __name__ == "__main__":
    main()
