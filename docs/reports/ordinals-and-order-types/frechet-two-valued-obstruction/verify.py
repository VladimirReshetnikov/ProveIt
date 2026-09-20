#!/usr/bin/env python3
"""Reproducible, exact supplementary checks for article.tex.

Scope: (1) integer identities used by the explicit infinite construction;
(2) finite-index analogues of the finite-pasting theorem. These checks are
NOT a proof of the infinite result and NOT a proof-assistant formalization.
In particular, a finite index set admits no proper filter containing all of
its cofinite subsets. Finite tests therefore concern arbitrary proper
principal filters, not objects of the paper's Frechet site.

Run: python3 verify.py --output verification_results.json
"""
from __future__ import annotations

import argparse
from itertools import combinations, product
import json
from pathlib import Path
import random
from typing import Dict, List, Sequence, Tuple

from obstruction_witness import contradiction_witness, in_row, in_tail, row_index


def require(condition: bool, message: str) -> None:
    # Deliberately not 'assert': checks remain active under python -O.
    if not condition:
        raise AssertionError(message)


def arithmetic_checks() -> Dict[str, int]:
    identities = 0
    for j in range(10000):
        n = row_index(j)
        require((j + 1) % (1 << n) == 0, "row divisibility")
        require(((j + 1) // (1 << n)) % 2 == 1, "row odd quotient")
        for m in range(15):
            require(in_tail(j, m) == (n >= m), "tail equals union of rows")
            identities += 1
    witness_cases = 0

    def check(m: int, n0: int, n1: int) -> None:
        nonlocal witness_cases
        r = contradiction_witness(m, n0, n1)
        j = r["j"]
        require(in_row(j, m), "witness not in the required row")
        require(in_tail(j, m), "witness not in the required tail")
        require(j >= max(n0, n1), "witness below a cutoff")
        require(j == (1 << m) * (2 * r["row_parameter"] + 1) - 1,
                "row parameter identity")
        require(r["row_parameter"] == 0 or j - r["period"] < max(n0, n1),
                "witness is not least")
        witness_cases += 1

    for m in range(13):
        for n0 in range(65):
            for n1 in range(65):
                check(m, n0, n1)
    rng = random.Random(20260920)
    for _ in range(10000):
        check(rng.randrange(201), rng.getrandbits(512), rng.getrandbits(512))
    invalid_cases = 0
    for args in [(-1, 0, 0), (0, -1, 0), (0, 0, -1), (True, 0, 0),
                 (0, 1.5, 0), (0, 0, "1")]:
        try:
            contradiction_witness(*args)
        except (TypeError, ValueError):
            invalid_cases += 1
        else:
            raise AssertionError("invalid argument accepted")
    return {"row_tail_identity_cases": identities,
            "cutoff_witness_cases": witness_cases,
            "invalid_input_cases": invalid_cases}


def finite_pasting_checks(n: int, alphabet_size: int, max_generators: int = 3) -> Dict[str, int]:
    """Exhaust all local sections on distinct nonempty principal kernels.

    F_K = {X: K subset X}; an equivalence class is exactly a function on K.
    Two kernels have a proper common extension iff their intersection is
    nonempty. Compatibility is equality on that intersection. The generated
    sieve covers the weakest proper filter iff the union of kernels is I.
    """
    kernels = [tuple(i for i in range(n) if mask & (1 << i))
               for mask in range(1, 1 << n)]
    global_sections = list(product(range(alphabet_size), repeat=n))
    families = configurations = compatible = covers = unique_cover_gluings = 0
    noncover_pastings = 0
    for size in range(1, min(max_generators, len(kernels)) + 1):
        for family in combinations(kernels, size):
            families += 1
            union = set().union(*map(set, family))
            covering = len(union) == n
            covers += int(covering)
            local_choices = [list(product(range(alphabet_size), repeat=len(k))) for k in family]
            for local_tuple in product(*local_choices):
                configurations += 1
                assignments = [dict(zip(k, values)) for k, values in zip(family, local_tuple)]
                consistent = all(
                    all(left[t] == right[t] for t in left.keys() & right.keys())
                    for left, right in combinations(assignments, 2)
                )
                if not consistent:
                    continue
                compatible += 1
                # Implement exactly the least-index finite pasting procedure.
                glued = tuple(next((a[t] for a in assignments if t in a), 0) for t in range(n))
                require(all(all(glued[t] == value for t, value in a.items()) for a in assignments),
                        "finite pasting failed")
                solutions = [f for f in global_sections
                             if all(all(f[t] == value for t, value in a.items()) for a in assignments)]
                require(glued in solutions, "constructed section absent from independent enumeration")
                require(len(solutions) == alphabet_size ** (n - len(union)),
                        "incorrect number of extensions")
                if covering:
                    require(len(solutions) == 1, "nonunique gluing for a finite cover")
                    unique_cover_gluings += 1
                else:
                    noncover_pastings += 1
    return {"index_size": n, "alphabet_size": alphabet_size,
            "max_generators": max_generators, "generator_families": families,
            "covering_generator_families": covers,
            "local_configurations": configurations,
            "compatible_configurations": compatible,
            "unique_cover_gluings": unique_cover_gluings,
            "noncover_pastings": noncover_pastings}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    finite = [finite_pasting_checks(n, 2) for n in range(1, 5)]
    finite += [finite_pasting_checks(n, 3) for n in range(1, 4)]
    result = {"schema_version": 1, "status": "PASS", "random_seed": 20260920,
              "scope": "Supplementary exact arithmetic and finite-index tests; not an infinite proof",
              "arithmetic": arithmetic_checks(), "finite_pasting": finite,
              "finite_totals": {key: sum(row[key] for row in finite) for key in
                                ["generator_families", "covering_generator_families", "local_configurations",
                                 "compatible_configurations", "unique_cover_gluings", "noncover_pastings"]}}
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
