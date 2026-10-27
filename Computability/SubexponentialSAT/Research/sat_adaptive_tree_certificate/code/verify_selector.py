#!/usr/bin/env python3
"""Compare the primary selector with independent directed-index operation costs."""
from itertools import permutations
import json
from random import Random

from portfolio import load_portfolios, select_plan
from verify_algebra import select_tree


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    rng = Random(261026)
    cases = 0
    seen = {}
    for entry in load_portfolios():
        r, trees = entry["groups"], entry["trees"]
        seen[str(r)] = set()
        for trial in range(120):
            dims = {e: rng.choice([1, 1, 1, 2, 3, 5, 7]) for e in permutations(range(r), 2)}
            if trial == 0:
                dims = {e: 1 for e in dims}
            expected_index, expected_scores = select_tree(r, trees, dims)
            actual = select_plan(r, dims, trees)
            require(actual["selected_plan_index"] == expected_index, "Tree selection disagreement")
            require(actual["all_plan_costs_power5"] == expected_scores, "Operation cost disagreement")
            seen[str(r)].add(expected_index)
            cases += 1
        dims = {e: 1 for e in permutations(range(r), 2)}
        for invalid in [0, -1, 1.5, True]:
            bad = dict(dims)
            bad[0, 1] = invalid
            try:
                select_plan(r, bad, trees)
            except ValueError:
                pass
            else:
                raise RuntimeError("Invalid list cardinality was accepted")
        bad = dict(dims)
        del bad[0, 1]
        try:
            select_plan(r, bad, trees)
        except ValueError:
            pass
        else:
            raise RuntimeError("Missing pair dimension was accepted")
    require(seen['9'] == {0,1,2} and seen['13'] == {0,1,2}, "Not all adaptive choices exercised")
    print(json.dumps({"status": "PASS", "exact_selection_cases": cases,
                      "invalid_inputs_rejected": 15,
                      "selected_plan_indices": {k: sorted(v) for k,v in seen.items()},
                      "oracle": "Independent operation-dimension predictor retaining directed indices"},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
