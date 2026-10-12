"""Independent small-instance oracle and reproducible operation-count audit."""

import itertools
import json
from pathlib import Path
import random
import time

from dual_forest_search import from_dense, solve_by_stopping, solve_degree_two
from dual_forest_verify import check_result


def no_stopping_subset(problem, surviving):
    """Exhaustive obstruction oracle, without a peeling algorithm."""
    surviving = list(surviving)
    for bits in range(1, 1 << len(surviving)):
        totals = {}
        for i, r in enumerate(surviving):
            if bits >> i & 1:
                for c, a in problem["rows"][r]:
                    totals[c] = totals.get(c, 0) + a
        if all(a != 1 for a in totals.values()):
            return False
    return True


def is_tree(problem, chosen):
    if len(chosen) != problem["vertices"] - 1:
        return False
    reached = {0}
    changed = True
    while changed:
        changed = False
        for e in chosen:
            edge = problem["edges"][e]
            if edge is None:
                return False
            a, b = edge
            if a in reached and b not in reached:
                reached.add(b)
                changed = True
            if b in reached and a not in reached:
                reached.add(a)
                changed = True
    return len(reached) == problem["vertices"]


def oracle(problem):
    eligible = [i for i, edge in enumerate(problem["edges"]) if edge is not None]
    r = problem["vertices"] - 1
    if r > len(eligible):
        return False
    for chosen in itertools.combinations(eligible, r):
        if is_tree(problem, chosen) and no_stopping_subset(
                problem, set(range(len(problem["rows"]))) - set(chosen)):
            return True
    return False


def within_degree_two(problem):
    owners = {}
    for row in problem["rows"]:
        for c, a in row:
            owners.setdefault(c, []).append(a)
    return all(len(values) <= 2 or 1 not in values for values in owners.values())


def audit():
    counters = {"cases": 0, "successes": 0, "negatives": 0,
                "degree_two_completed": 0, "degree_two_outside_regime": 0,
                "search_proof_replays": 0, "degree_two_proof_replays": 0}

    def check(problem):
        expected = oracle(problem)
        search = solve_by_stopping(problem)
        if search["status"] == "INCONCLUSIVE":
            raise AssertionError(("unexpected search cap", problem, search))
        assert (search["status"] == "SUCCESS") == expected, (problem, search, expected)
        accepted, reason = check_result(problem, search)
        assert accepted, (problem, search, reason)
        counters["search_proof_replays"] += 1
        poly = solve_degree_two(problem)
        if poly["status"] == "INCONCLUSIVE":
            assert not within_degree_two(problem), (problem, poly)
            counters["degree_two_outside_regime"] += 1
        else:
            assert (poly["status"] == "SUCCESS") == expected, (problem, poly, expected)
            accepted, reason = check_result(problem, poly)
            assert accepted, (problem, poly, reason)
            counters["degree_two_completed"] += 1
            counters["degree_two_proof_replays"] += 1
        counters["cases"] += 1
        counters["successes" if expected else "negatives"] += 1

    families = {}
    before = counters["cases"]
    choices = [None, [0, 0], [0, 1], [1, 1]]
    for m in range(5):
        for edges in itertools.product(choices, repeat=m):
            for column in itertools.product(range(3), repeat=m):
                check(from_dense(2, list(edges), [[a] for a in column]))
    families["all_two_vertex_multigraphs_up_to_four_rows_one_column"] = counters["cases"] - before

    before = counters["cases"]
    graphs = [
        [[0, 1], [1, 2], [0, 2]],
        [[0, 1], [1, 2], [0, 1]],
        [[0, 1], [1, 2], None],
        [[0, 1], [1, 2], [2, 2]],
        [[0, 1], [0, 1], [0, 1]],
        [[0, 0], [1, 2], None],
    ]
    for edges in graphs:
        for entries in itertools.product(range(3), repeat=6):
            matrix = [list(entries[i:i + 2]) for i in range(0, 6, 2)]
            check(from_dense(3, edges, matrix))
    families["six_three_row_graphs_all_two_column_matrices"] = counters["cases"] - before

    rng = random.Random(0xC0F0E57)
    for name, count, degree_two in (("random_degree_two", 5000, True),
                                     ("random_general", 2000, False)):
        before = counters["cases"]
        for _ in range(count):
            m, h = rng.randrange(1, 9), rng.randrange(8)
            v = rng.randrange(1, min(5, m + 1) + 1)
            edges = [[i, i + 1] for i in range(v - 1)]
            edges.extend(None if rng.randrange(5) == 0 else [rng.randrange(v), rng.randrange(v)]
                         for _ in range(m - v + 1))
            rng.shuffle(edges)
            matrix = [[0] * h for _ in range(m)]
            if degree_two:
                for c in range(h):
                    if rng.randrange(8) == 0:
                        for r in rng.sample(range(m), rng.randrange(m + 1)):
                            matrix[r][c] = 2
                    else:
                        for r in rng.sample(range(m), rng.randrange(min(2, m) + 1)):
                            matrix[r][c] = rng.randrange(1, 3)
            else:
                matrix = [[rng.choices((0, 1, 2), (5, 4, 1))[0] for _ in range(h)] for _ in range(m)]
            check(from_dense(v, edges, matrix, columns=h))
        families[name] = counters["cases"] - before
    return {"all_passed": True, "families": families, **counters}


def main():
    started = time.perf_counter()
    result = audit()
    result["elapsed_seconds"] = time.perf_counter() - started
    Path("results").mkdir(exist_ok=True)
    Path("results/audit.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
