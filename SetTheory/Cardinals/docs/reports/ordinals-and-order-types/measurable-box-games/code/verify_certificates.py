#!/usr/bin/env python3
"""Exact finite checks accompanying 'Countable Information, Uncountably Many Boxes'.

Python 3.10+; standard library only.  No network access is used.
This is an independent executable check, not a Lean/Rocq proof.

Run: python verify_certificates.py --output verification_report.json
     python verify_certificates.py --check certificates.json

Vertices are integers 0 <= v < 2**n; coordinate i is bit i (LSB = 0).
A matching is a tuple of disjoint sorted vertex pairs, sorted by first vertex.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from collections import Counter
from decimal import Decimal, localcontext
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Iterator

Edge = tuple[int, int]
Matching = tuple[Edge, ...]
Output = tuple[int, int]
Table = tuple[Output, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def matchings(n: int) -> Iterator[Matching]:
    """Enumerate every perfect matching exactly once by least free vertex."""
    require(1 <= n <= 5, "exhaustive matching enumeration supports 1 <= n <= 5")
    def visit(mask: int, edges: tuple[Edge, ...]) -> Iterator[Matching]:
        if mask == 0:
            yield tuple(sorted(edges))
            return
        low = mask & -mask
        v = low.bit_length() - 1
        rest = mask ^ low
        for i in range(n):
            w = v ^ (1 << i)
            if rest & (1 << w):
                yield from visit(rest ^ (1 << w), edges + ((min(v, w), max(v, w)),))
    yield from visit((1 << (1 << n)) - 1, ())


def direction(edge: Edge) -> int:
    z = edge[0] ^ edge[1]
    require(z > 0 and (z & (z - 1)) == 0, "edge is not a cube edge")
    return z.bit_length() - 1


def check_matching(n: int, matching: Matching) -> None:
    vertices = [v for edge in matching for v in edge]
    require(sorted(vertices) == list(range(1 << n)), "matching does not cover once")
    for edge in matching:
        require(0 <= direction(edge) < n, "invalid direction")


@lru_cache(maxsize=None)
def sliceable(matching: Matching, free: tuple[int, ...]) -> bool:
    """Decision-tree realizability of a matching on a specified subcube."""
    if len(matching) == 1:
        return direction(matching[0]) in free
    used = {direction(edge) for edge in matching}
    for i in free:
        if i in used:
            continue
        newfree = tuple(j for j in free if j != i)
        halves = tuple(tuple(edge for edge in matching if ((edge[0] >> i) & 1) == b)
                       for b in (0, 1))
        if all(sliceable(half, newfree) for half in halves):
            return True
    return False


def matching_count_dp(n: int) -> int:
    """Exact permanent DP for the bipartite n-cube; practical for n <= 5."""
    require(1 <= n <= 5, "matching DP supports 1 <= n <= 5")
    left = [v for v in range(1 << n) if v.bit_count() % 2 == 0]
    right = [v for v in range(1 << n) if v.bit_count() % 2 == 1]
    index = {v: j for j, v in enumerate(right)}
    neighbors = [sum(1 << index[v ^ (1 << i)] for i in range(n)) for v in left]
    @lru_cache(maxsize=None)
    def count(mask: int) -> int:
        row = mask.bit_count()
        if row == len(left):
            return 1
        options = neighbors[row] & ~mask
        total = 0
        while options:
            bit = options & -options
            options ^= bit
            total += count(mask | bit)
        return total
    return count(0)


def sliceable_counts(nmax: int, q: int = 2) -> list[int]:
    """Proved inclusion-exclusion recurrence for q-ary line partitions."""
    require(nmax >= 1 and q >= 2, "nmax >= 1 and q >= 2 required")
    f = [0, 1]
    for n in range(2, nmax + 1):
        f.append(sum((-1) ** (k + 1) * math.comb(n, k) * f[n-k] ** (q ** k)
                     for k in range(1, n)))
        require(f[-1] > 0, "recurrence produced a nonpositive value")
    return f


def blind_table(n: int, q: int, table: Table) -> bool:
    xs = tuple(product(range(q), repeat=n))
    if len(table) != len(xs):
        return False
    lookup = dict(zip(xs, table))
    for x, out in zip(xs, table):
        i, a = out
        if not (0 <= i < n and 0 <= a < q):
            return False
        for v in range(q):
            y = x[:i] + (v,) + x[i+1:]
            if lookup[y] != out:
                return False
    return True


def success_vector(n: int, q: int, table: Table) -> tuple[int, ...]:
    require(blind_table(n, q, table), "non-blind table")
    return tuple(int(x[i] == a) for x, (i, a)
                 in zip(product(range(q), repeat=n), table))


def table_from_matching(n: int, matching: Matching, guesses: tuple[int, ...]) -> Table:
    check_matching(n, matching)
    require(len(guesses) == len(matching) and set(guesses) <= {0, 1}, "bad guesses")
    lookup: dict[tuple[int, ...], Output] = {}
    for edge, a in zip(matching, guesses):
        i = direction(edge)
        for v in edge:
            x = tuple((v >> j) & 1 for j in range(n))
            lookup[x] = (i, a)
    return tuple(lookup[x] for x in product(range(2), repeat=n))


def finite_checks() -> tuple[dict, dict]:
    report: dict = {"status": "all exact checks passed", "matching_counts": [],
                    "two_box_team_checks": [], "balanced_list_checks": 0}
    cert: dict = {"format_version": 1, "bit_coordinate_convention": "LSB is coordinate 0"}
    counts = sliceable_counts(20)
    nonsliceable_example: Matching | None = None
    for n in range(1, 5):
        total = legal = 0
        all_directions = 0
        for matching in matchings(n):
            check_matching(n, matching)
            total += 1
            good = sliceable(matching, tuple(range(n)))
            legal += int(good)
            if len({direction(e) for e in matching}) == n:
                all_directions += 1
                if n == 4 and nonsliceable_example is None:
                    nonsliceable_example = matching
            if n <= 3:
                require(good, "unexpected small nonsliceable matching")
        require(legal == counts[n], f"recurrence disagrees with enumeration at n={n}")
        report["matching_counts"].append({"n": n, "all": total, "sliceable": legal,
                                           "nonsliceable": total - legal,
                                           "using_all_directions": all_directions,
                                           "blind_output_maps": total * 2 ** (2 ** (n-1)),
                                           "legal_output_maps": legal * 2 ** (2 ** (n-1))})
    require(nonsliceable_example is not None, "missing four-box witness")
    witness = nonsliceable_example
    require(not sliceable(witness, (0, 1, 2, 3)), "witness unexpectedly sliceable")
    witness_table = table_from_matching(4, witness, (0,) * 8)
    require(blind_table(4, 2, witness_table), "witness is not blind")
    cert["four_box_nonrealizable_matching"] = [list(e) for e in witness]
    cert["four_box_guesses"] = [0] * 8

    # This tiny exhaustive test does not rely on the matching parametrization.
    outs = tuple(product(range(2), range(2)))
    tables = [t for t in product(outs, repeat=4) if blind_table(2, 2, t)]
    require(len(tables) == 8, "unexpected two-box blind-table count")
    vectors = [success_vector(2, 2, t) for t in tables]
    require(all(sum(v) == 2 for v in vectors), "finite averaging failed")
    for m in range(1, 5):
        histogram: Counter[int] = Counter()
        majority_max = 0
        for team in product(range(len(tables)), repeat=m):
            scores = [sum(vectors[p][j] for p in team) for j in range(4)]
            require(sum(scores) == 2*m, "team averaging failed")
            require(min(scores) <= m // 2, "minimax upper bound failed")
            histogram[min(scores)] += 1
            if m == 3:
                majority_max = max(majority_max, sum(z >= 2 for z in scores))
        row = {"players": m, "teams": len(tables)**m,
               "minimum_score_histogram": dict(sorted(histogram.items()))}
        if m == 3:
            require(majority_max == 3, "majority probability check failed")
            row["maximum_majority_probability"] = "3/4"
        report["two_box_team_checks"].append(row)

    # An explicitly executable three-box team, each player reads one other box.
    xs = tuple(product(range(2), repeat=3))
    team = [tuple((p, 1-x[(p+1) % 3]) for x in xs) for p in range(3)]
    sv = [success_vector(3, 2, t) for t in team]
    scores = [sum(v[j] for v in sv) for j in range(8)]
    require(Counter(scores) == Counter({0: 2, 2: 6}), "cyclic example failed")
    cert["cyclic_three_box_team"] = {"q": 2, "n": 3,
        "configurations": [list(x) for x in xs],
        "tables": [[[i, a] for i, a in t] for t in team], "scores": scores}
    report["cyclic_three_box_score_histogram"] = dict(sorted(Counter(scores).items()))

    for q in range(2, 13):
        for r in range(1, q):
            for m in range(1, 21):
                lists = [{(p*r + j) % q for j in range(r)} for p in range(m)]
                require(all(len(a) == r for a in lists), "bad list size")
                scores = [sum(v in a for a in lists) for v in range(q)]
                require(min(scores) == (m*r)//q, "balanced list bound failed")
                report["balanced_list_checks"] += 1
    all_counts = [0] + [matching_count_dp(n) for n in range(1, 6)]
    require(all_counts[1:] == [1, 2, 9, 272, 589185], "permanent DP mismatch")
    b6 = sum((-1)**(k+1) * math.comb(6, k) * all_counts[6-k]**(2**k)
             for k in range(1, 6))
    require(b6 == 2001589252896, "six-cube lower count mismatch")
    require(49 * counts[6] < 6 * b6, "exact rarity inequality failed")
    report["all_matching_counts_dp_1_to_5"] = all_counts[1:]
    report["six_cube_matchings_with_unused_direction"] = b6
    report["rarity_bound_ratio_exact"] = {"numerator": 49*counts[6],
                                            "denominator": 6*b6}
    report["binary_sliceable_counts_1_to_12"] = [str(v) for v in counts[1:13]]
    report["ternary_sliceable_counts_1_to_5"] = [str(v) for v in sliceable_counts(5, 3)[1:]]
    with localcontext() as ctx:
        ctx.prec = 65
        n = 20
        scale = Decimal(2) ** (-n)
        a = Decimal(counts[n]).ln() * scale
        lower = a + scale * (Decimal(n+1).ln() + (1-Decimal(2)/n).ln())
        upper = a + scale * (Decimal(n+1).ln() + Decimal(1)/(n+1))
        # These are rounded evaluations of the proved symbolic bounds, NOT an
        # interval-arithmetic proof of the displayed decimal endpoints.
        report["gamma_bounds_symbolic"] = {
            "N": n,
            "lower": "2^-N * (log(F_N) + log(N+1) + log(1-2/N))",
            "upper": "2^-N * (log(F_N) + log(N+1) + 1/(N+1))",
            "lower_decimal_rounded": str(lower), "upper_decimal_rounded": str(upper),
            "decimal_status": "65-digit rounded evaluations; symbolic bounds are proved"}
    return report, cert


def check_external(path: Path) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    require(data.get("format_version") == 1, "unsupported certificate version")
    matching = tuple(tuple(map(int, e)) for e in data["four_box_nonrealizable_matching"])
    check_matching(4, matching)
    require(len({direction(e) for e in matching}) == 4, "not all four directions used")
    require(not sliceable(matching, (0, 1, 2, 3)), "matching is realizable")
    require(blind_table(4, 2, table_from_matching(4, matching,
                tuple(data["four_box_guesses"]))), "invalid witness output map")
    obj = data["cyclic_three_box_team"]
    require(obj["q"] == 2 and obj["n"] == 3, "wrong team dimensions")
    require(obj["configurations"] == [list(x) for x in product(range(2), repeat=3)],
            "wrong configuration order")
    vectors = [success_vector(3, 2, tuple(tuple(z) for z in t)) for t in obj["tables"]]
    scores = [sum(v[j] for v in vectors) for j in range(8)]
    require(scores == obj["scores"], "score certificate mismatch")
    require(Counter(scores) == Counter({0: 2, 2: 6}), "wrong score distribution")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_report.json"))
    parser.add_argument("--certificates", type=Path, default=Path("certificates.json"))
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    if args.check is not None:
        check_external(args.check)
        print(f"Certificate accepted: {args.check}")
        return
    report, cert = finite_checks()
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    args.certificates.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
    check_external(args.certificates)
    print(json.dumps({"status": report["status"],
                      "matching_counts": report["matching_counts"],
                      "balanced_list_checks": report["balanced_list_checks"]}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
