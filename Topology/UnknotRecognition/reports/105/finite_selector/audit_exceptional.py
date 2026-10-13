"""Independent exhaustive tree/peeling oracle for the new FPT selector."""

import argparse
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import random
import time

from exceptional_forest import solve_exceptional, _partial_partitions


def is_tree(problem, chosen):
    n = problem["vertices"]
    if len(chosen) != n - 1:
        return False
    adjacency = [[] for _ in range(n)]
    for r in chosen:
        edge = problem["edges"][r]
        if edge is None or edge[0] == edge[1]:
            return False
        a, b = edge
        adjacency[a].append(b)
        adjacency[b].append(a)
    seen, todo = {0}, [0]
    while todo:
        for v in adjacency[todo.pop()]:
            if v not in seen:
                seen.add(v)
                todo.append(v)
    return len(seen) == n


def literal_peel(problem, tree):
    rows = [dict(row) for row in problem["rows"]]
    live = set(range(len(rows))) - set(tree)
    trace = []
    while live:
        for c in range(problem["columns"]):
            occurrences = [(r, rows[r].get(c, 0)) for r in live]
            if sum(a for _, a in occurrences) == 1:
                r = next(r for r, a in occurrences if a)
                live.remove(r)
                trace.append([r, c])
                break
        else:
            return False, trace, sorted(live)
    return True, trace, []


def brute(problem):
    for tree in combinations(range(len(problem["rows"])), problem["vertices"] - 1):
        if is_tree(problem, tree) and literal_peel(problem, tree)[0]:
            return list(tree)
    return None


def check_trace(problem, certificate):
    tree = certificate["tree"]
    if len(tree) != len(set(tree)) or not is_tree(problem, tree):
        return False
    rows = [dict(row) for row in problem["rows"]]
    live = set(range(len(rows))) - set(tree)
    used = set()
    for r, c in certificate["peeling"]:
        if r not in live or c in used or not 0 <= c < problem["columns"]:
            return False
        if rows[r].get(c, 0) != 1:
            return False
        if sum(rows[s].get(c, 0) for s in live) != 1:
            return False
        live.remove(r)
        used.add(c)
    return not live


def encode(vertices, edges, dense, width=None):
    columns = width if width is not None else len(dense[0]) if dense else 0
    return dict(vertices=vertices, columns=columns, edges=edges,
                rows=[[[c, a] for c, a in enumerate(row) if a] for row in dense])


class Audit:
    def __init__(self):
        self.counts = Counter()
        self.parameters = Counter()
        self.max_partitions = 0
        self.start = time.perf_counter()

    def case(self, problem, family):
        expected = brute(problem)
        result = solve_exceptional(problem)
        yes = result["status"] == "SUCCESS"
        if result["status"] == "INCONCLUSIVE" or yes != (expected is not None):
            raise AssertionError(json.dumps(dict(problem=problem, expected=expected,
                                                  actual=result), indent=2))
        if yes and not check_trace(problem, result["certificate"]):
            raise AssertionError("independent trace replay failed")
        self.counts[family] += 1
        self.counts["success" if yes else "no_forest"] += 1
        self.parameters[result.get("parameters", {}).get("interface_rows", "disconnected")] += 1
        self.max_partitions = max(self.max_partitions,
                                  result["stats"].get("partial_partitions", 0))

    def export(self):
        return dict(counts=dict(self.counts),
                    interface_histogram={str(k): v for k, v in self.parameters.items()},
                    max_partitions=self.max_partitions,
                    elapsed_seconds=time.perf_counter() - self.start)


def exhaustive(audit):
    edge_options = [None, [0, 0], [0, 1], [1, 1]]
    # 4^3 possible two-vertex edge records, including ineligibility and loops;
    # all 3^(3*2) nonnegative occurrence matrices with entries 0,1,2.
    for edges in product(edge_options, repeat=3):
        for entries in product(range(3), repeat=6):
            dense = [entries[2*r:2*r+2] for r in range(3)]
            audit.case(encode(2, list(edges), dense), "exhaustive_3x2")


def randomized(audit, count, seed):
    rng = random.Random(seed)
    for _ in range(count):
        n = rng.randrange(1, 5)
        m, c = rng.randrange(0, 7), rng.randrange(0, 7)
        edges = [None if rng.random() < .12 else [rng.randrange(n), rng.randrange(n)]
                 for _ in range(m)]
        dense = [[rng.choices([0, 1, 2, 3, 11], [10, 10, 3, 1, 1])[0]
                  for _ in range(c)] for _ in range(m)]
        audit.case(encode(n, edges, dense, c), "random_general")


def cycle_compatible(audit, count, seed):
    rng = random.Random(seed)
    for _ in range(count):
        n, m = rng.randrange(1, 5), rng.randrange(1, 7)
        edges = [[rng.randrange(n), rng.randrange(n)] for _ in range(m)]
        cycles = []
        for size in (1, 2, 3):
            for support in combinations(range(m), size):
                parity = [0] * n
                for r in support:
                    for v in edges[r]:
                        parity[v] ^= 1
                if not any(parity):
                    cycles.append(support)
        selected = rng.sample(cycles, min(len(cycles), rng.randrange(0, 7)))
        dense = [[int(r in support) for support in selected] for r in range(m)]
        audit.case(encode(n, edges, dense), "random_cycle_compatible")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--output", default="audit_results.json")
    args = parser.parse_args()
    audit = Audit()
    bells = [1, 2, 5, 15, 52, 203, 877]
    observed = [len(list(_partial_partitions([1 << i for i in range(u)])))
                for u in range(7)]
    if observed != bells:
        raise AssertionError((observed, bells))
    if not args.quick:
        exhaustive(audit)
    randomized(audit, 100 if args.quick else 2000, 20261012)
    cycle_compatible(audit, 100 if args.quick else 2000, 99137)
    # An empty graph is connected exactly in the one-vertex namespace.
    audit.case(encode(1, [], [], 0), "edge_cases")
    audit.case(encode(2, [], [], 0), "edge_cases")
    triangle = encode(3, [[0, 1], [1, 2], [0, 2]], [[1], [1], [1]])
    for option in ({"max_work": 0}, {"max_partitions": 0}):
        if solve_exceptional(triangle, **option)["status"] != "INCONCLUSIVE":
            raise AssertionError("budget exhaustion produced a conclusive result")
    result = dict(audit.export(), partial_partition_counts=observed,
                  independent_oracle="enumerate all spanning trees; literal uncapped peeling",
                  random_seeds=[20261012, 99137], budget_checks=2, mismatches=0,
                  geometric_scope="abstract graph/matrix inputs; no claimed native realization")
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
