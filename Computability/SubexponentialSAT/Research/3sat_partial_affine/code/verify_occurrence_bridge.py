#!/usr/bin/env python3
"""Finite exact checks for the occurrence-preserving 3-SAT bridge.

This is an exponential tiny-instance identity checker, not a fast SAT solver.
It independently sums Boolean wire assignments in each branched network and
compares the result with ordinary assignment enumeration.
"""

from itertools import combinations, combinations_with_replacement, product
import json
from math import ceil, log2
from pathlib import Path
import random


def normalize(clauses):
    output = []
    for clause in clauses:
        values = set(clause)
        if any(-literal in values for literal in values):
            continue
        output.append(tuple(sorted(values)))
    return output


def count_formula(n, clauses):
    return sum(all(any(bool(bits[abs(lit) - 1]) == (lit > 0)
                       for lit in clause) for clause in clauses)
               for bits in product((0, 1), repeat=n))


def count_wire_network(clauses, fixed):
    # Constant-one clauses retain their unfixed original incidences.
    edges = [(index, lit) for index, clause in enumerate(clauses)
             for lit in clause if abs(lit) not in fixed]
    count = 0
    for bits in product((0, 1), repeat=len(edges)):
        known = dict(fixed)
        consistent = True
        for (_, lit), bit in zip(edges, bits):
            variable = abs(lit)
            if variable in known and known[variable] != bit:
                consistent = False
                break
            known[variable] = bit
        if not consistent:
            continue
        count += all(any(bool(known[abs(lit)]) == (lit > 0)
                         for lit in clause) for clause in clauses)
    return count, len(edges)


def count_bridge(n, raw_clauses, threshold):
    clauses = normalize(raw_clauses)
    if any(not clause for clause in clauses):
        return 0, 0, 0
    degree = {}
    for clause in clauses:
        for lit in clause:
            degree[abs(lit)] = degree.get(abs(lit), 0) + 1
    heavy = sorted(v for v, d in degree.items() if d > threshold)
    total = 0
    maximum_wires = 0
    for bits in product((0, 1), repeat=len(heavy)):
        branch, wires = count_wire_network(clauses, dict(zip(heavy, bits)))
        total += branch
        maximum_wires = max(maximum_wires, wires)
    return total * 2 ** (n - len(degree)), maximum_wires, len(heavy)


def main():
    cases = []
    clause_pool = []
    for width in range(1, 4):
        for variables in combinations(range(1, 4), width):
            clause_pool += [tuple(v * sign for v, sign in zip(variables, signs))
                            for signs in product((-1, 1), repeat=width)]
    cases.append((3, []))
    cases += [(3, [clause]) for clause in clause_pool]
    cases += [(3, list(clauses)) for clauses in
              combinations_with_replacement(clause_pool, 2)]
    rng = random.Random(317260)
    for _ in range(100):
        n = rng.randrange(3, 6)
        clauses = []
        for _ in range(rng.randrange(1, 5)):
            variables = rng.sample(range(1, n + 1), rng.randrange(1, 4))
            clauses.append(tuple(v * rng.choice((-1, 1)) for v in variables))
        cases.append((n, clauses))
    cases += [
        (6, [(1, 2), (1, -2), (1, 3), (1, -3)]),
        (4, [(1, -1, 2), (2, 2, 3)]),
        (5, [()]),
        (7, []),
        (4, [(1,), (-1,), (2, 3, 4)]),
    ]
    comparisons = 0
    for n, clauses in cases:
        expected = count_formula(n, clauses)
        normalized = normalize(clauses)
        L = sum(map(len, normalized))
        thresholds = sorted({1, 2, max(1, ceil(log2(L + 1)))})
        for threshold in thresholds:
            actual, wires, heavy = count_bridge(n, clauses, threshold)
            if actual != expected:
                raise RuntimeError((n, clauses, threshold, actual, expected))
            if wires > L:
                raise RuntimeError("Wire-count inequality failed")
            if heavy * (threshold + 1) > L:
                raise RuntimeError("Branch-count inequality failed")
            comparisons += 1
    output = {
        "status": "passed",
        "formula_cases": len(cases),
        "exact_comparisons": comparisons,
        "wire_equality_checked": True,
        "unused_variables_checked": True,
        "constant_clause_ports_retained": True,
        "scope": "Tiny finite identity checks; no complete fast contractor implemented.",
        "seed": 317260,
    }
    output_path = Path(__file__).resolve().parents[1] / "results" / "occurrence_bridge_checks.json"
    output_path.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
