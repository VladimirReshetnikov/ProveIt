#!/usr/bin/env python3
"""Audit new finite solvers on independently reconstructed native exports.

The input exporter authenticates source geometry; this script audits only the
exported rooted graph and unsigned matrix.  Full native whole-cut packets are
checked separately by the lower-forest adapter audit.
"""

import argparse
from collections import Counter
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time


def brute(problem, limit=50000):
    """Independent tiny oracle: explicit vertex blocks and literal column sums."""
    eligible = [i for i, edge in enumerate(problem["edges"])
                if edge is not None and edge[0] != edge[1]]
    rank = problem["vertices"] - 1
    candidates = math.comb(len(eligible), rank) if len(eligible) >= rank else 0
    if candidates > limit:
        return dict(status="NOT_RUN", candidate_subsets=candidates)
    trees, successful = 0, 0
    for chosen in itertools.combinations(eligible, rank):
        blocks = [{i} for i in range(problem["vertices"])]
        for row in chosen:
            edge = problem["edges"][row]
            left = next(i for i, block in enumerate(blocks) if edge[0] in block)
            right = next(i for i, block in enumerate(blocks) if edge[1] in block)
            if left == right:
                break
            blocks[left].update(blocks[right])
            del blocks[right]
        else:
            if len(blocks) != 1:
                continue
            trees += 1
            live = set(range(len(problem["rows"]))) - set(chosen)
            while live:
                totals, owner = {}, {}
                for row in live:
                    for column, value in problem["rows"][row]:
                        totals[column] = totals.get(column, 0) + value
                        owner[column] = row
                pivot = next((c for c in totals if totals[c] == 1), None)
                if pivot is None:
                    break
                live.remove(owner[pivot])
            successful += not live
    return dict(status="EXHAUSTIVE", candidate_subsets=candidates, trees=trees,
                successful_trees=successful, feasible=bool(successful))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fast", type=Path, required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.fast.resolve()))
    from triple_forest_research import base, base_verify, nonlinear, solver

    source_bytes = args.input.read_bytes()
    source = json.loads(source_bytes)
    report = dict(source_pin=source["source_pin"], corpus_sha256=source["corpus_sha256"],
                  exported_input_sha256=hashlib.sha256(source_bytes).hexdigest(),
                  seed=20261012, cases=[])
    summaries = {name: dict(parameters={}, outcomes={}) for name in ("canonical", "optimal")}
    start = time.perf_counter()
    for case_number, case in enumerate(source["cases"]):
        record = dict(id=case["id"], variants={})
        for variant, field in (("canonical", "problem"), ("optimal", "optimized_problem")):
            problem = case[field]
            data, work = base.normalize(problem), base.Work()
            prepared, special, mandatory = nonlinear._special_state(data, work)
            ideals = nonlinear._ideal_masks(prepared, special, work)
            parameters = dict(rows=len(data[3]), vertices=data[0],
                              k=len(prepared["triples"]),
                              t=len({row for _, rows, _ in prepared["triples"] for row in rows}),
                              d=len(special), J=len(ideals), mandatory_groups=len(mandatory))
            results = {}
            calls = {
                "degree_two": lambda: base.solve_degree_two(problem),
                "history": lambda: solver.solve(problem, max_work=5_000_000),
                "boolean_ideal": lambda: nonlinear.solve_boolean(problem, seed=20261012+case_number,
                                      max_work=20_000_000, max_states=100_000, trials=2),
                "deterministic_width": lambda: nonlinear.solve_width(problem, max_work=5_000_000),
            }
            for name, call in calls.items():
                tick = time.perf_counter()
                result = call()
                result["audit_seconds"] = time.perf_counter() - tick
                if result["status"] == "SUCCESS":
                    assert base_verify.verify(problem, result), (case["id"], variant, name)
                    result["independent_replay"] = True
                results[name] = result
            oracle = brute(problem)
            if oracle["status"] == "EXHAUSTIVE":
                for name in ("history", "deterministic_width"):
                    result = results[name]
                    if result["status"] != "INCONCLUSIVE":
                        assert (result["status"] == "SUCCESS") == oracle["feasible"], (case["id"], name)
                if results["boolean_ideal"]["status"] == "SUCCESS":
                    assert oracle["feasible"]
            record["variants"][variant] = dict(parameters=parameters, results=results, oracle=oracle)
        report["cases"].append(record)
    for variant in summaries:
        records = [case["variants"][variant] for case in report["cases"]]
        summaries[variant]["parameters"] = {
            key: dict(sorted(Counter(record["parameters"][key] for record in records).items()))
            for key in ("k", "t", "d", "J", "mandatory_groups")}
        summaries[variant]["outcomes"] = {
            name: dict(Counter(record["results"][name]["status"] for record in records))
            for name in ("degree_two", "history", "boolean_ideal", "deterministic_width")}
        summaries[variant]["oracle"] = dict(Counter(record["oracle"]["status"] for record in records))
    report.update(summary=summaries, elapsed_seconds=time.perf_counter()-start)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report["summary"], indent=2))


if __name__ == "__main__":
    main()
