#!/usr/bin/env python3
"""Deterministically author the shipped finite fixtures; not run by verification.

This is a transparent fixture-authoring aid, not an oracle or part of the test
command. Keep the reviewed snapshots under version control. Small OEIS counts
are independently transcribed, rather than calculated by this file.
"""
from fractions import Fraction as Q
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def write(name, data):
    (ROOT / name).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def entries(values):
    return [{"a": a, "b": b, "value": str(v)} for (a, b), v in sorted(values.items())]


def build(name, n, cutoff, nonsingletons, singletons):
    q = {(a, b): Q(0) for a in range(1, n + 1) for b in range(a, n + 1)}
    q.update({key: Q(value) for key, value in nonsingletons.items()})
    q.update({(i, i): Q(value) for i, value in singletons.items()})
    # Direct nonsingleton complement, independently of q+singleton-deficit.
    completed = dict(q)
    for i in range(1, n + 1):
        completed[i, i] = i - sum(v for (a, b), v in q.items() if a < b and a <= i <= b)
    rules = [{"j": j, "changes": entries({(j, j + 1): Q(-1), (j, j): Q(1), (j + 1, j + 1): Q(1)})}
             for j in range(cutoff, n)]
    # Independent row formula: cut j+1 minus flow crossing from earlier rows.
    rows = [Q(j + 1) - sum(v for (a, b), v in q.items() if a <= j and b >= j + 1)
            for j in range(n)]
    choices = {}
    for j in range(cutoff, n):
        low, high = rows[j], rows[j] + q[j, j + 1] / 2
        choices[str(j)] = [k for k in range(j + 2) if low <= k <= high]
    records = []
    for selected in itertools.product(*choices.values()):
        alpha = list(rows)
        for j, rho in zip(range(cutoff, n), selected):
            alpha[j] = Q(rho)
        beta = [v - 1 for v in alpha[1:]] + [Q(n)]
        records.append({"alpha": list(map(str, alpha)), "beta": list(map(str, beta))})
    digest = hashlib.sha256(json.dumps(records, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    expected = {"n": n, "cutoff_M": cutoff,
                "q_cut_loads": [str(sum(v for (a, b), v in q.items() if a <= i <= b)) for i in range(1, n + 1)],
                "cut_loads": list(map(str, range(1, n + 1))),
                "netflow": ["1"] * n + [str(-n)], "rows": list(map(str, rows)),
                "columns": list(map(str, [v - 1 for v in rows[1:]] + [Q(n)])),
                "triangle_choices": choices, "choice_product": len(records), "margin_vector_sha256": digest}
    return {"name": name, "n": n, "cutoff_M": cutoff, "q": entries(q), "completed": entries(completed), "triangles": rules}, expected


def main():
    specs = [
        ("rational_four_triangles", 12, 8,
         {(8, 9): "4", (9, 10): "17/4", (10, 11): "19/4", (11, 12): "5", (8, 11): "1/3", (9, 12): "1/6"},
         {i: Q(1, i + 1) for i in range(8, 13)}),
        ("rational_endpoint", 5, 3, {(3, 4): "3/2", (4, 5): "2", (3, 5): "1/4"}, {i: "1/5" for i in range(3, 6)}),
        ("saturated_edges", 4, 2, {(2, 3): "2", (3, 4): "1"}, {}),
        ("no_triangle_boundary", 2, 2, {}, {2: "2"}),
    ]
    fixtures, snapshots = [], {}
    for spec in specs:
        fixture, expected = build(*spec)
        fixtures.append(fixture)
        snapshots[spec[0]] = expected
    write("rational_fixtures.json", {"schema_version": 1,
          "scope": "Purpose-built finite rational arrays. Not samples or approximations of the exponential profile; not asymptotic evidence.",
          "fixtures": fixtures})
    write("expected_checks.json", {"schema_version": 1, "sequence_source": "https://oeis.org/A008608",
          "indexing": "OEIS starts at n=1. n=0 has the separately stated empty-array convention a_0=1.",
          "small_counts": {str(n): value for n, value in enumerate([1, 1, 2, 7, 40, 357, 4820, 96030])},
          "fixtures": snapshots})


if __name__ == "__main__":
    main()
