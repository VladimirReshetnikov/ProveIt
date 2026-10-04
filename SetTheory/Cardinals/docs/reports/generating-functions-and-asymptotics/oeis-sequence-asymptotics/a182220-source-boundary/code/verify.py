#!/usr/bin/env python3
"""Exact checks for the source boundary of extensional acyclic digraphs.
Python 3.10+, standard library only. This is testing, not a proof assistant.
Run: python verify.py --max-n 64 --brute-n 7
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any


def choose(n: int, k: int) -> int:
    """Combinatorial binomial; impossible choices have value zero."""
    return math.comb(n, k) if 0 <= k <= n else 0


def ceil_log2(n: int) -> int:
    if n < 1:
        raise ValueError("n must be positive")
    return (n - 1).bit_length()


def full_sets(max_n: int) -> list[int]:
    u = [1]
    for n in range(1, max_n + 1):
        u.append(sum((-1) ** (n-m-1) * choose((1 << m)-m, n-m) * u[m]
                     for m in range(n)))
    return u


def source_sieve(n: int, k: int, u: list[int]) -> int:
    """Unlabeled count, obtained from marked-source binomial inversion."""
    if n == 0:
        return int(k == 0)
    if k < 1 or k > n:
        return 0
    return sum((-1) ** (t-k) * choose(t, k)
               * choose((1 << (n-t))-(n-t), t) * u[n-t]
               for t in range(k, n+1))


def deletion_triangle(max_n: int) -> list[list[int]]:
    """Independent source-deletion recurrence: Tomescu, Corollary 2.1.7."""
    rows = [[1], [0, 1]]
    for n in range(2, max_n+1):
        row = [0] * (n+1)
        old = rows[-1]
        for s in range(1, n):
            num = ((1 << (n-s))-(n-1)) * old[s-1]
            num += sum(choose(s+j, j+1) * (1 << (n-1-s-j)) * old[s+j]
                       for j in range(n-s))
            assert num % s == 0, (n, s, "nonintegral deletion")
            row[s] = num // s
        rows.append(row)
    return rows[:max_n+1]


def defect_count(n: int, d: int, u: list[int]) -> int:
    q = ceil_log2(n)
    m, k = q+d, n-q-d
    if k < 1:
        return 0
    return sum((-1) ** j * choose(k+j, j)
               * choose((1 << (m-j))-(m-j), k+j) * u[m-j]
               for j in range(d+1))


def enumerate_dags(n: int) -> tuple[Counter[int], dict[tuple[int, int], int], int]:
    """Exhaust all DAGs with edges i->j, j<i; canonicalize by finite collapse.
    Every isomorphism class has such an ordering. Equal neighborhoods are
    rejected, and nested frozensets identify isomorphic surviving graphs.
    No integer Ackermann encoding (whose size can be enormous) is used.
    """
    seen: dict[frozenset[Any], tuple[int, int]] = {}
    masks: list[int] = []
    shapes: list[frozenset[Any]] = []
    total = 0

    def visit(i: int, targets: int, arcs: int) -> None:
        nonlocal total
        if i == n:
            total += 1
            key = frozenset(shapes)
            value = (n - targets.bit_count(), arcs)
            if key in seen:
                assert seen[key] == value
            else:
                seen[key] = value
            return
        forbidden = set(masks)
        for mask in range(1 << i):
            if mask in forbidden:
                continue
            shape = frozenset(shapes[j] for j in range(i) if mask >> j & 1)
            assert shape not in shapes
            masks.append(mask)
            shapes.append(shape)
            visit(i+1, targets | mask, arcs + mask.bit_count())
            shapes.pop()
            masks.pop()
    visit(0, 0, 0)
    by_source: Counter[int] = Counter(s for s, e in seen.values())
    by_both: Counter[tuple[int, int]] = Counter(seen.values())
    return by_source, dict(by_both), total


def core_edge_polynomial(m: int, k: int) -> Counter[int]:
    """Direct boundary construction, using canonical increasing mask cores.
    Canonical mask codes x_0<...<x_(m-1), x_i<2^i enumerate full sets.
    For m<=3, enumerate every chosen source-neighborhood family explicitly.
    """
    import itertools
    result: Counter[int] = Counter()
    def cores(prefix: tuple[int, ...]):
        i = len(prefix)
        if i == m:
            yield prefix
            return
        lo = prefix[-1]+1 if prefix else 0
        for x in range(lo, 1 << i):
            yield from cores(prefix + (x,))
    for core in cores(()):
        avail = [s for s in range(1 << m) if s not in core]
        core_arcs = sum(s.bit_count() for s in core)
        for selected in itertools.combinations(avail, k):
            result[core_arcs + sum(s.bit_count() for s in selected)] += 1
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=64)
    parser.add_argument("--brute-n", type=int, default=7)
    parser.add_argument("--out", type=Path, default=Path(__file__).parent / "data")
    args = parser.parse_args()
    if args.max_n < 16 or not 0 <= args.brute_n <= 7:
        parser.error("require --max-n >=16 and 0 <= --brute-n <=7")
    args.out.mkdir(parents=True, exist_ok=True)
    u = full_sets(args.max_n)
    expected_u = [1, 1, 1, 2, 9, 88, 1802, 75598, 6421599, 1097780312,
                  376516036188, 258683018091900, 355735062429124915,
                  978786413996934006272, 5387230452634185460127166,
                  59308424712939278997978128490,
                  1305926814154452720947815884466579]
    assert u[:17] == expected_u
    rows = deletion_triangle(args.max_n)
    checks = Counter()
    for n in range(1, args.max_n+1):
        q = ceil_log2(n)
        assert sum(rows[n]) == u[n]
        for k in range(1, n+1):
            value = source_sieve(n, k, u)
            assert value == rows[n][k], (n, k, "sieve vs deletion")
            assert (value > 0) == (k <= n-q), (n, k, "support")
            checks["sieve_deletion_cells"] += 1
            m = n-k
            lead = u[m] * choose((1 << m)-m, k)
            assert value <= lead
            assert (lead-value) * (1 << k) <= m * lead, (n, k, "coverage")
            checks["coverage_cells"] += 1
        extremal = u[q] * choose((1 << q)-q, n-q)
        assert rows[n][n-q] == extremal
        checks["extremal_counts"] += 1
        for d in range(min(6, n-q)):
            assert defect_count(n, d, u) == rows[n][n-q-d]
            checks["finite_defect_counts"] += 1
    expected_labeled = [1, 2, 12, 192, 24, 8160, 2400, 898560, 384480,
                       14400, 245145600, 126040320, 9777600, 50400,
                       159035627520, 90043269120, 9660672000,
                       179222400, 80640, 237882053283840,
                       141969202744320, 17961178152960, 547498828800,
                       2586608640, 802369403419852800]
    flat = [value * math.factorial(n) for n in range(1,11)
            for value in rows[n][1:] if value]
    assert flat[:25] == expected_labeled
    brute = []
    for n in range(1, args.brute_n+1):
        by_source, by_both, total = enumerate_dags(n)
        assert sum(by_source.values()) == u[n]
        assert all(by_source.get(k, 0) == rows[n][k] for k in range(n+1))
        q, k = ceil_log2(n), n-ceil_log2(n)
        predicted = core_edge_polynomial(q, k)
        observed = Counter({e: count for (s,e),count in by_both.items() if s == k})
        assert observed == predicted, (n, "boundary arc polynomial")
        brute.append({"n": n, "topologically_labeled_graphs": total,
                      "isomorphism_classes": sum(by_source.values()),
                      "source_row": dict(sorted(by_source.items())),
                      "extremal_arc_distribution": dict(sorted(observed.items()))})
    with (args.out / "boundary_counts.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["n", "ceil_log2_n", "max_sources", "b0_unlabeled",
                    "b1_unlabeled", "b2_unlabeled", "b0_labeled"])
        for n in range(1, args.max_n+1):
            q = ceil_log2(n)
            b = [defect_count(n,d,u) for d in range(3)]
            w.writerow([n,q,n-q,*b,b[0]*math.factorial(n)])
    with (args.out / "source_triangle.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["n","sources","unlabeled","labeled"])
        for n in range(1,args.max_n+1):
            for k,value in enumerate(rows[n]):
                if value:
                    w.writerow([n,k,value,value*math.factorial(n)])
    report = {"status": "all assertions passed", "max_n": args.max_n,
              "brute_n": args.brute_n, "exact_checks": dict(checks),
              "oeis_checks": {"A001192_terms":17,"A182162_terms":25},
              "brute_force":brute,
              "scope": "Finite checks, not a formal proof or novelty certification."}
    (args.out / "verification.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))

if __name__ == "__main__":
    main()
