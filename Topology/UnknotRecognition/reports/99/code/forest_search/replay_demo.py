"""Deterministic supplied-graph proof replay; Python standard library only."""

from copy import deepcopy
import json
from pathlib import Path

from dual_forest_search import solve_by_stopping, solve_degree_two
from dual_forest_verify import check_result


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    root = Path(__file__).resolve().parent / "examples"
    replayed = []
    mutations = 0
    for name, expected in (("positive", "SUCCESS"), ("negative", "NO_FOREST")):
        problem = json.loads((root / (name + "_problem.json")).read_text())
        for method, solver in (("degree_two", solve_degree_two),
                               ("stopping_search", solve_by_stopping)):
            record = json.loads((root / (name + "_" + method + ".json")).read_text())
            accepted, reason = check_result(problem, record)
            require(accepted, reason)
            require(record["status"] == expected, "unexpected stored status")
            regenerated = solver(problem)
            require(regenerated["status"] == record["status"], "status drift")
            require(regenerated["certificate"] == record["certificate"], "proof drift")
            replayed.append({"example": name, "method": method, "status": expected})

            bad = deepcopy(record)
            if expected == "SUCCESS":
                bad["certificate"]["tree"] = [0]
            elif method == "degree_two":
                bad["certificate"]["rank"] += 1
            else:
                bad["certificate"]["children"] = []
            require(not check_result(problem, bad)[0], "mutated proof was accepted")
            mutations += 1

    print(json.dumps({
        "all_passed": True,
        "replayed_and_regenerated": replayed,
        "rejected_mutations": mutations,
        "negative_scope": "No dual spanning tree admits complete raw peeling in the supplied graph/matrix; no manifold or knot conclusion."
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
