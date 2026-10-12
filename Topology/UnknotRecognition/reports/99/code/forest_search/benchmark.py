"""Controlled supplied-query comparison with source-independent tree enumeration.

Every timed positive arm returns a tree and peeling sequence and runs the
same independent checker.  No native knot-recognition performance is claimed.
"""

import json
from pathlib import Path
import platform
import statistics
import time

from dual_forest_search import from_dense, solve_by_stopping, solve_degree_two
from dual_forest_verify import verify


def parallel_chain(k, negative=False):
    edges, matrix = [], []
    for i in range(k):
        for value in (2 if negative and i == 0 else 1, 2):
            edges.append([i, i + 1])
            row = [0] * k
            row[i] = value
            matrix.append(row)
    return from_dense(k + 1, edges, matrix)


def enumerate_trees(problem):
    edges, rows = problem["edges"], problem["rows"]
    required = problem["vertices"] - 1
    eligible = [e for e, edge in enumerate(edges) if edge is not None]
    counts = {"search_nodes": 0, "candidate_trees": 0,
              "graph_edge_visits": 0, "peel_incidence_visits": 0}

    def rank(selected):
        blocks = []
        answer = 0
        for e in selected:
            counts["graph_edge_visits"] += 1
            a, b = edges[e]
            ai = next((i for i, block in enumerate(blocks) if a in block), None)
            bi = next((i for i, block in enumerate(blocks) if b in block), None)
            if a == b or ai is not None and ai == bi:
                continue
            answer += 1
            if ai is None and bi is None:
                blocks.append({a, b})
            elif ai is None:
                blocks[bi].add(a)
            elif bi is None:
                blocks[ai].add(b)
            else:
                blocks[ai].update(blocks[bi])
                del blocks[bi]
        return answer

    def leaf_test(tree):
        live = set(range(len(rows))) - set(tree)
        schedule = []
        while live:
            totals, owners = {}, {}
            for r in sorted(live):
                for c, a in rows[r]:
                    counts["peel_incidence_visits"] += 1
                    totals[c] = totals.get(c, 0) + a
                    owners[c] = r
            column = next((c for c in sorted(totals) if totals[c] == 1), None)
            if column is None:
                return None
            row = owners[column]
            live.remove(row)
            schedule.append([row, column])
        return schedule

    def search(index, chosen):
        counts["search_nodes"] += 1
        if len(chosen) == required:
            counts["candidate_trees"] += 1
            schedule = leaf_test(chosen)
            if schedule is not None:
                return {"kind": "success", "tree": chosen, "peeling": schedule}
            return None
        if len(chosen) + len(eligible) - index < required:
            return None
        if rank(chosen + eligible[index:]) < required:
            return None
        edge = eligible[index]
        if rank(chosen + [edge]) == len(chosen) + 1:
            result = search(index + 1, chosen + [edge])
            if result is not None:
                return result
        return search(index + 1, chosen)

    proof = search(0, [])
    counts["counted_work"] = sum(counts.values())
    result = {"status": "SUCCESS" if proof is not None else "NO_FOREST", "stats": counts}
    if proof is not None:
        result["certificate"] = proof
    return result


def timed(problem, solver):
    start = time.perf_counter_ns()
    result = solver(problem)
    assert result["status"] == "SUCCESS"
    assert verify(problem, result)
    return (time.perf_counter_ns() - start) / 1e6, result


def main():
    rounds = 5
    records = []
    solvers = {"enumeration": enumerate_trees, "degree_two": solve_degree_two,
               "stopping_search": solve_by_stopping}
    for k in (1, 2, 4, 6, 8, 10, 12):
        problem = parallel_chain(k)
        times = {name: [] for name in (*solvers, "enumeration_control")}
        outputs = {}
        for round_id in range(rounds):
            order = list(solvers.items())
            if round_id % 2:
                order.reverse()
            for name, solver in order:
                elapsed, result = timed(problem, solver)
                times[name].append(elapsed)
                outputs[name] = result
            elapsed, _ = timed(problem, enumerate_trees)
            times["enumeration_control"].append(elapsed)
        assert outputs["enumeration"]["stats"]["candidate_trees"] == 2**k
        medians = {name: statistics.median(values) for name, values in times.items()}
        record = {"rank": k, "rows": 2 * k, "incidences": 2 * k,
                  "times_ms": times, "median_ms": medians,
                  "enumeration_over_degree_two": medians["enumeration"] / medians["degree_two"],
                  "enumeration_over_search": medians["enumeration"] / medians["stopping_search"],
                  "aa_enumeration_ratio": medians["enumeration"] / medians["enumeration_control"],
                  "operation_counts": {name: result["stats"] for name, result in outputs.items()}}
        records.append(record)
        print(k, medians, flush=True)
    negatives = []
    for k in (2, 4, 8, 12):
        problem = parallel_chain(k, negative=True)
        values = {name: solver(problem) for name, solver in solvers.items()}
        assert all(result["status"] == "NO_FOREST" for result in values.values())
        assert verify(problem, values["degree_two"])
        assert verify(problem, values["stopping_search"])
        assert values["enumeration"]["stats"]["candidate_trees"] == 2**k
        negatives.append({"rank": k, "operation_counts": {
            name: result["stats"] for name, result in values.items()},
            "rado_certificate": values["degree_two"]["certificate"]})
    large = []
    for k in (16, 32, 64, 128):
        elapsed, result = timed(parallel_chain(k), solve_degree_two)
        large.append({"rank": k, "elapsed_ms": elapsed, "operation_counts": result["stats"],
                      "naive_candidate_trees_formula": "2^" + str(k)})
    payload = {"environment": {"python": platform.python_version(), "platform": platform.platform()},
               "rounds": rounds, "positive_paired_queries": records,
               "negative_operation_counts": negatives, "large_polynomial_only": large,
               "scope": "supplied graph/matrix query plus positive replay; no native knot benchmarks"}
    Path("results").mkdir(exist_ok=True)
    Path("results/benchmark.json").write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    lines = ["rank,rows,incidences,trees,enum_ms,degree2_ms,search_ms,enum_over_degree2,aa"]
    for record in records:
        med = record["median_ms"]
        lines.append(",".join(str(x) for x in (record["rank"], record["rows"], record["incidences"],
            record["operation_counts"]["enumeration"]["candidate_trees"], med["enumeration"],
            med["degree_two"], med["stopping_search"], record["enumeration_over_degree_two"],
            record["aa_enumeration_ratio"])))
    Path("results/benchmark.csv").write_text("\n".join(lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
