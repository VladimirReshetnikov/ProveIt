#!/usr/bin/env python3
"""Independent verifier for the six-state shuffle proof.

Python 3.9+; standard library only.  Default: certificates + exhaustive coverage
+ auxiliary lemma checks.  --quick checks certificates without completeness.
The C++ search executable is not invoked or trusted.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Set, Tuple

Cell = Tuple[int, int]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def popcount(value: int) -> int:
    return bin(value).count("1")


def cells(columns: Iterable[int], m: int) -> Set[Cell]:
    return {(i, j) for j, mask in enumerate(columns)
            for i in range(m) if mask & (1 << i)}


def image(points: Iterable[Cell], f: Tuple[int, ...],
          g: Tuple[int, ...]) -> Set[Cell]:
    result: Set[Cell] = set()
    for i, j in points:
        result.add((f[i], j))
        result.add((i, g[j]))
    return result


def balanced_triple(columns: Tuple[int, ...]):
    for i, j, k in itertools.combinations(range(len(columns)), 3):
        a, b, c = columns[i], columns[j], columns[k]
        if (a | b) == (a | c) == (b | c):
            return i, j, k
    return None


def antichain(sets: Iterable[frozenset]) -> bool:
    sets = tuple(sets)
    return all(not (a <= b or b <= a)
               for a, b in itertools.combinations(sets, 2))


def load_certificates(path: Path) -> List[dict]:
    records = []
    for line_no, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("|")
        require(len(parts) == 5, f"line {line_no}: expected five fields")
        m, n, key = map(int, parts[0].split())
        columns, f, g, pre = [tuple(map(int, part.split())) for part in parts[1:]]
        require(2 <= m <= 6 and m <= n, f"line {line_no}: dimensions")
        require(len(columns) == len(g) == len(pre) == n, "column dimensions")
        require(tuple(sorted(f)) == tuple(range(m)), "row permutation")
        require(tuple(sorted(g)) == tuple(range(n)), "column permutation")
        require(tuple(sorted(set(columns))) == columns, "target column ordering")
        require(all(0 < x < (1 << m) for x in columns + pre), "mask range")
        require(sum(1 << x for x in columns) == key, "family key")
        S, T = cells(columns, m), cells(pre, m)
        col_sets = tuple(frozenset(i for i in range(m) if x & (1 << i))
                         for x in columns)
        row_sets = tuple(frozenset(j for j, x in enumerate(columns)
                                  if x & (1 << i)) for i in range(m))
        require(antichain(col_sets) and antichain(row_sets), "not a double antichain")
        require(all(len(s) >= 2 for s in col_sets + row_sets), "degree below two")
        require(balanced_triple(columns) is None, "balanced triple in residual")
        require(len(T) < len(S), "predecessor is not smaller")
        require({i for i, _ in T} == set(range(m)), "predecessor misses a row")
        require({j for _, j in T} == set(range(n)), "predecessor misses a column")
        require(image(T, f, g) == S, "transition identity fails")
        records.append(dict(m=m, n=n, key=key, columns=columns,
                            f=f, g=g, predecessor=pre))
    return records


def orbit_tables(records: List[dict]):
    """Map each row-renaming orbit member to a certificate and the renaming."""
    tables: Dict[int, Dict[Tuple[int, ...], Tuple[int, Tuple[int, ...]]]] = {
        m: {} for m in range(2, 7)}
    perms = {m: tuple(itertools.permutations(range(m))) for m in range(2, 7)}
    for index, record in enumerate(records):
        m = record["m"]
        table = tables[m]
        own_keys = set()
        for p in perms[m]:
            renamed = tuple(sorted(sum(1 << p[i] for i in range(m)
                                       if mask & (1 << i))
                                   for mask in record["columns"]))
            if renamed in own_keys:
                continue
            require(renamed not in table, "duplicate certificate orbit")
            own_keys.add(renamed)
            table[renamed] = (index, p)
    return tables


def exhaustive_coverage(tables):
    """Enumerate residual antichains using ordinary sets, not C++ bitsets.

    Every candidate family is visited in increasing column-mask order.
    Rejection of comparability or a balanced triple is hereditary under adding
    columns, so it cannot discard a family that would later become admissible.
    """
    counts = Counter()
    visits = {}
    for m in range(2, 7):
        values = tuple(x for x in range(1, (1 << m) - 1) if popcount(x) >= 2)
        supports = {x: frozenset(i for i in range(m) if x & (1 << i)) for x in values}
        table = tables[m]
        nodes = 0
        checked = 0

        def visit(chosen: Tuple[int, ...], candidates: Tuple[int, ...]) -> None:
            nonlocal nodes, checked
            nodes += 1
            n = len(chosen)
            if n >= m:
                rows = tuple(frozenset(j for j, x in enumerate(chosen)
                                      if i in supports[x]) for i in range(m))
                if all(len(row) >= 2 for row in rows) and antichain(rows):
                    require(chosen in table, f"uncovered family m={m}: {chosen}")
                    counts[(m, n)] += 1
                    checked += 1
            for position, x in enumerate(candidates):
                X = supports[x]
                forbidden = False
                for a, b in itertools.combinations(chosen, 2):
                    A, B = supports[a], supports[b]
                    if A | B == A | X == B | X:
                        forbidden = True
                        break
                if forbidden:
                    continue
                remaining = tuple(y for y in candidates[position + 1:]
                                  if not (supports[y] <= X or X <= supports[y]))
                visit(chosen + (x,), remaining)

        visit((), values)
        require(checked == len(table), f"orbit coverage count mismatch for m={m}")
        visits[m] = nodes
        print(f"m={m}: enumerated {nodes} residual-antichain prefixes; "
              f"covered {checked} row-labelled column families")
    return counts, visits


def auxiliary_checks() -> dict:
    tested = Counter()
    # Balanced-triple contraction, using literal coordinate sets.
    for m in range(2, 7):
        for columns in itertools.combinations(range(1, (1 << m) - 1), 3):
            A = tuple(frozenset(i for i in range(m) if x & (1 << i))
                      for x in columns)
            if not antichain(A) or not (A[0] | A[1] == A[0] | A[2] == A[1] | A[2]):
                continue
            pre = (columns[0] & columns[1], columns[1] & columns[2],
                   columns[2] & columns[0])
            S, T = cells(columns, m), cells(pre, m)
            require(image(T, tuple(range(m)), (1, 2, 0)) == S, "triple image")
            require(len(T) < len(S), "triple strictness")
            require({i for i, _ in T} == {i for i, _ in S}, "triple row support")
            require({j for _, j in T} == {0, 1, 2}, "triple column support")
            tested["balanced_triples"] += 1
    # Isolated-edge seeding, including all four origin positions.
    for m in range(2, 7):
        for n in range(2, 7):
            for r0, c0, p, q in itertools.product(range(m), range(n), range(m), range(n)):
                r = r0 if r0 != p else next(i for i in range(m) if i != p)
                c = c0 if c0 != q else next(j for j in range(n) if j != q)
                f, g = list(range(m)), list(range(n))
                f[p], f[r] = f[r], f[p]
                g[q], g[c] = g[c], g[q]
                power = 2 if (r0 == p) == (c0 == q) else 1
                result = {(r0, c0)}
                for _ in range(power):
                    result = image(result, tuple(f), tuple(g))
                require(result == {(p, q), (r, c)}, "isolated-edge seed")
                tested["isolated_edge_seeds"] += 1
    # Two-letter isolation of each cell: test on every singleton input.
    for m in range(2, 7):
        for n in range(2, 7):
            rf, cf = m - 1, n - 1
            for p, q in itertools.product(range(m), range(n)):
                a_f = tuple(rf if i == p else 0 for i in range(m))
                a_g = (next(j for j in range(n) if j != q),) * n
                b_f = (0,) * m
                b_g = tuple(cf if j == q else 0 for j in range(n))
                for i, j in itertools.product(range(m), range(n)):
                    result = image(image({(i, j)}, a_f, a_g), b_f, b_g)
                    require(((rf, cf) in result) == ((i, j) == (p, q)), "cell isolation")
                    tested["cell_isolation_tests"] += 1
    return dict(tested)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificates", type=Path,
                        default=Path(__file__).with_name("certificates.tsv"))
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    records = load_certificates(args.certificates)
    print(f"Verified {len(records)} strict full-support predecessor certificates.")
    summary = {"certificate_count": len(records),
               "certificate_sha256": hashlib.sha256(args.certificates.read_bytes()).hexdigest(),
               "exhaustive": not args.quick,
               "representatives": {f"{m}x{n}": count for (m, n), count in
                                   sorted(Counter((r['m'], r['n']) for r in records).items())}}
    if not args.quick:
        tables = orbit_tables(records)
        counts, visits = exhaustive_coverage(tables)
        summary["labelled_residual_matrices"] = {
            f"{m}x{n}": count for (m, n), count in sorted(counts.items())}
        summary["enumerated_prefixes"] = visits
        summary["auxiliary_checks"] = auxiliary_checks()
        print("Auxiliary checks:", summary["auxiliary_checks"])
        print("PASS: certificates, exhaustive coverage, and auxiliary checks.")
    if args.json:
        args.json.write_text(json.dumps(summary, indent=2) + "\n")

if __name__ == "__main__":
    main()
