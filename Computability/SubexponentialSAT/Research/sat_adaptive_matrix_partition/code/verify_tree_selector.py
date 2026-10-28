"""Check minimax dynamic programming against an independent exhaustive oracle."""
import json
from itertools import combinations
from pathlib import Path
import random
from adaptive_tree import optimal_balanced_tree, leaf_paths, all_balanced_trees


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    rng = random.Random(2026102616)
    trees = tuple(all_balanced_trees(tuple(range(8))))
    require(len(trees) == 315, "incorrect exhaustive tree count")
    records = []
    for case in range(12):
        weights = {e: rng.randrange(0, 101) for e in combinations(range(8), 2)}
        tree, optimum, stats = optimal_balanced_tree(weights, 8)
        oracle = min(max(cost for _, cost in leaf_paths(t, weights)) for t in trees)
        require(optimum == oracle, "DP and exhaustive optimum differ")
        require(max(cost for _, cost in leaf_paths(tree, weights)) == optimum,
                "reconstructed tree has wrong score")
        require(stats["states"] == 107 and stats["unordered_splits"] == 273,
                "unexpected eight-group state/split count")
        records.append({"case": case, "optimum": optimum, **stats})

    sixteen = []
    for kind in ("uniform", "random", "concentrated"):
        weights = {e: (1 if kind == "uniform" else
                       rng.randrange(0, 1001) if kind == "random" else
                       (1000 if 0 in e else 0))
                   for e in combinations(range(16), 2)}
        tree, optimum, stats = optimal_balanced_tree(weights, 16)
        require(stats["states"] == 14827 and stats["unordered_splits"] == 462465,
                "unexpected sixteen-group state/split count")
        require(max(cost for _, cost in leaf_paths(tree, weights)) == optimum,
                "sixteen-group tree reconstruction failed")
        # Exact consequence of the proved moment inequality for arbitrary w.
        require(21 * optimum**2 <= 1450 * sum(w*w for w in weights.values()),
                "tree optimum violates analytic moment bound")
        if kind == "uniform":
            require(optimum == 85, "uniform path cardinality is not 85")
        sixteen.append({"kind": kind, "optimum": optimum, **stats})

    result = {"status": "pass", "exhaustive_eight_group_trees": len(trees),
              "eight_group_profiles": records, "sixteen_group_profiles": sixteen,
              "scope": "Tests exact minimax tree selection; no SAT runtime is measured."}
    path = Path(__file__).resolve().parents[1] / "results" / "tree_selector.json"
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "pass", "exhaustive_tree_count": len(trees),
                      "eight_group_profiles": len(records),
                      "sixteen_group_profiles": sixteen}, indent=2))


if __name__ == "__main__":
    main()
