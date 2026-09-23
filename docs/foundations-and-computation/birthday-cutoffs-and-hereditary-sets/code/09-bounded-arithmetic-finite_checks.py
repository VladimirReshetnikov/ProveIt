#!/usr/bin/env python3
"""Finite regression checks for surreal_cutoffs.tex; not transfinite proofs.

Uses only Python's standard library. Run with Python 3.10 or later.
The JSON report is written next to this script. Failed checks raise an error.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path
from typing import FrozenSet


def check_prefix_bits(max_length: int = 6) -> dict[str, int]:
    signs = [s for n in range(max_length + 1)
             for s in itertools.product((-1, 1), repeat=n)]
    signs.sort(key=lambda s: s + (0,) * (max_length - len(s)))
    pos = {s: i for i, s in enumerate(signs)}
    prefix_cases = bit_cases = 0
    for x in signs:
        for y in signs:
            lo, hi = sorted((pos[x], pos[y]))
            formula = all(len(z) > len(x)
                          for z in signs[lo:hi + 1] if z != x)
            actual = len(x) <= len(y) and y[:len(x)] == x
            assert formula == actual, ("prefix", x, y, formula, actual)
            prefix_cases += 1
        for a in range(len(x)):
            prefix = x[:a]
            formula = pos[prefix] < pos[x]
            assert formula == (x[a] == 1), ("bit", x, a)
            bit_cases += 1
    return {"maximum_sign_length": max_length, "sign_sequences": len(signs),
            "prefix_pairs": prefix_cases, "bit_positions": bit_cases}


def check_pairing(max_domain: int = 32) -> dict[str, int]:
    cases = 0
    for theta in range(1, max_domain + 1):
        values = [theta * i + j for i in range(theta) for j in range(theta)]
        assert len(set(values)) == theta * theta
        assert all(0 <= value < theta * theta + theta for value in values)
        cases += len(values)
    return {"maximum_finite_domain": max_domain, "ordered_pairs": cases}


def edge(mask: int, n: int, i: int, j: int) -> bool:
    return bool(mask & (1 << (n * i + j)))


def well_founded(mask: int, n: int) -> bool:
    # Every nonempty subset contains an E-minimal member.
    return all(any((subset >> j) & 1 and
                   all(not ((subset >> i) & 1) or not edge(mask, n, i, j)
                       for i in range(n)) for j in range(n))
               for subset in range(1, 1 << n))


def extensional(mask: int, n: int) -> bool:
    predecessors = [tuple(edge(mask, n, i, j) for i in range(n))
                    for j in range(n)]
    return len(set(predecessors)) == n


def root_generated_formula(mask: int, n: int, root: int) -> bool:
    for subset in range(1 << n):
        if not (subset >> root) & 1:
            continue
        downward_closed = all(not ((subset >> j) & 1) or
                              not edge(mask, n, i, j) or (subset >> i) & 1
                              for i in range(n) for j in range(n))
        if downward_closed and subset != (1 << n) - 1:
            return False
    return True


def reachable(mask: int, n: int, root: int) -> set[int]:
    reached = {root}
    while True:
        new = reached | {i for j in reached for i in range(n)
                         if edge(mask, n, i, j)}
        if new == reached:
            return reached
        reached = new


def collapse(mask: int, n: int) -> dict[int, FrozenSet]:
    result: dict[int, FrozenSet] = {}
    while len(result) < n:
        progress = False
        for j in range(n):
            if j in result:
                continue
            pred = [i for i in range(n) if edge(mask, n, i, j)]
            if all(i in result for i in pred):
                result[j] = frozenset(result[i] for i in pred)
                progress = True
        assert progress, "collapse called on a non-well-founded relation"
    return result


# A finite code consists of node count, relation mask, and root.
Code = tuple[int, int, int]


def embedding(c: Code, d: Code, f: tuple[int, ...], *, full: bool) -> bool:
    n, r, t = c
    m, s, u = d
    if len(f) != n or len(set(f)) != n or not all(0 <= v < m for v in f):
        return False
    if not edge(s, m, f[t], u):
        return False
    if not all(edge(r, n, i, j) == edge(s, m, f[i], f[j])
               for i in range(n) for j in range(n)):
        return False
    if full and not all(not edge(s, m, v, f[j]) or
                        any(f[i] == v and edge(r, n, i, j) for i in range(n))
                        for v in range(m) for j in range(n)):
        return False
    return True


def check_codes(max_nodes: int = 3) -> dict[str, int | bool]:
    codes: list[Code] = []
    decoded: dict[Code, FrozenSet] = {}
    relation_cases = root_cases = encoding_cases = 0
    for n in range(1, max_nodes + 1):
        for r in range(1 << (n * n)):
            relation_cases += 1
            bits = tuple(bool(r & (1 << k)) for k in range(n * n + n))
            assert not any(bits[n * n:])
            assert all(bits[n * i + j] == edge(r, n, i, j)
                       for i in range(n) for j in range(n))
            encoding_cases += 1
            wf, ext = well_founded(r, n), extensional(r, n)
            values = collapse(r, n) if wf and ext else None
            for t in range(n):
                root_cases += 1
                generated = root_generated_formula(r, n, t)
                assert generated == (len(reachable(r, n, t)) == n)
                if wf and ext and generated:
                    c = (n, r, t)
                    codes.append(c)
                    assert values is not None
                    assert len(set(values.values())) == n
                    decoded[c] = values[t]
    equality_cases = membership_cases = 0
    for c in codes:
        for d in codes:
            n, r, t = c
            m, s, u = d
            iso = n == m and any(
                f[t] == u and all(edge(r, n, i, j) == edge(s, m, f[i], f[j])
                                  for i in range(n) for j in range(n))
                for f in itertools.permutations(range(m), n))
            member = any(embedding(c, d, f, full=True)
                         for f in itertools.permutations(range(m), n))
            assert iso == (decoded[c] == decoded[d]), ("equality", c, d)
            assert member == (decoded[c] in decoded[d]), ("membership", c, d)
            equality_cases += 1
            membership_cases += 1
    # Empty set embedded into the middle node of the 3-node singleton chain.
    c = (1, 0, 0)
    d = (3, (1 << 1) | (1 << 5), 2)  # 0 E 1 E 2
    f = (1,)
    assert c in decoded and d in decoded
    assert decoded[c] not in decoded[d]
    assert embedding(c, d, f, full=False)
    assert not embedding(c, d, f, full=True)
    return {"maximum_nodes": max_nodes, "relations": relation_cases,
            "rooted_relations": root_cases, "bit_encodings": encoding_cases,
            "valid_codes": len(codes), "equality_code_pairs": equality_cases,
            "membership_code_pairs": membership_cases,
            "missing_predecessor_fullness_counterexample_confirmed": True}


def main() -> None:
    report = {
        "status": "PASS",
        "prefix_and_bit_tests": check_prefix_bits(),
        "finite_pairing_tests": check_pairing(),
        "finite_relation_code_tests": check_codes(),
        "scope": [
            "Finite exhaustive regression checks for the indicated bounds.",
            "Not a proof of transfinite coding, cardinal bounds, or bi-interpretation.",
            "No Lean or other proof-assistant certification is claimed.",
        ],
    }
    path = Path(__file__).resolve().with_name("verification_report.json")
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
