"""Compare adaptive aggregation with exhaustive finite tensor contractions."""
import json
import random
from itertools import product
from math import log2, sqrt
from pathlib import Path
from adaptive_groups import (DIRECTED_PAIRS, PARTITIONS, VERTICES, DualRing,
                             contract_nine, direct_contraction, select_partition)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    rng = random.Random(20261026)
    require(len(PARTITIONS) == 280, "wrong partition count")
    require(len(set(PARTITIONS)) == 280, "duplicate partition")
    records = []
    for case in range(32):
        precision = 1 + case % 7
        ring = DualRing(precision)
        # Up to twelve nontrivial pair lists; exact total sizes <= 2^12 or 3^6.
        edges = rng.sample(list(DIRECTED_PAIRS), case % 13)
        dimensions = {e: (3 if case % 5 == 0 and len(edges) <= 6 else 2)
                      for e in edges}
        tables = {}
        for v in VERTICES:
            incident = sorted(e for e in edges if v in e)
            tables[v] = {
                key: (rng.randrange(ring.modulus), rng.randrange(ring.modulus))
                for key in product(*(range(dimensions[e]) for e in incident))
            }
        got, stats = contract_nine(dimensions, tables, ring)
        expected = direct_contraction(dimensions, tables, ring)
        require(got == expected, f"finite contraction mismatch in case {case}")
        records.append({"case": case, "precision": precision,
                        "nontrivial_pairs": len(edges), "result": list(got), **stats})

    # Independently test the analytic triangle bound on arbitrary list sizes.
    # Floating checks are supplementary; the exact covariance proof is separate.
    profiles = []
    for case in range(128):
        dimensions = {e: rng.randrange(1, 1000001) if case % 3 else
                      (1 << rng.randrange(0, 161)) for e in DIRECTED_PAIRS}
        chosen = select_partition(dimensions)
        hs = [log2(x) for x in chosen[3]]
        objective = sum(hs) - 0.6 * min(hs)
        norm = sqrt(sum(log2(d)**2 for d in dimensions.values()))
        bound = sqrt(4617 / 175) * norm
        require(objective <= bound + 1e-8, "triangle inequality failed")
        profiles.append(objective / norm if norm else 0)

    result = {
        "status": "pass", "partition_count": 280,
        "finite_contractions": len(records),
        "ring": "(Z/2^p Z)[V]/(V^2), p=1..7",
        "random_triangle_profiles": len(profiles),
        "largest_observed_triangle_to_directed_l2_ratio": max(profiles),
        "analytic_ratio_bound": sqrt(4617 / 175),
        "records": records,
        "scope": "Tests the aggregation identity and exact partition selector; not an end-to-end SAT solver, fast matrix implementation, or proof of the imported contraction theorem."
    }
    target = Path(__file__).resolve().parents[1] / "results" / "group_contraction.json"
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "records"}, indent=2))


if __name__ == "__main__":
    main()
