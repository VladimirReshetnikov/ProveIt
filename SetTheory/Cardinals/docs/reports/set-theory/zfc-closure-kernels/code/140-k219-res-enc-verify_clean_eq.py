#!/usr/bin/env python3
"""Independent finite CFG checks for the reconstructed equality macros.

This is a diagnostic, not the unbounded proof.  The latter is in
../../report/sections/equality.tex for search hit 10.
"""
from pathlib import Path
import hashlib
import json
import random

HERE = Path(__file__).resolve().parent


def leaves(tree, path=""):
    if isinstance(tree[0], str):
        return [(path, tree[0], tree[1])]
    return leaves(tree[0], path + "0") + leaves(tree[1], path + "1")


def compile_cfg(tree):
    rows = leaves(tree)
    intervals = {}
    by_path = {p: i for i, (p, _, _) in enumerate(rows)}

    def interval(path):
        if path in by_path:
            i = by_path[path]
            out = (i, i + 1)
        else:
            left, right = interval(path + "0"), interval(path + "1")
            assert left[1] == right[0]
            out = (left[0], right[1])
        intervals[path] = out
        return out

    interval("")

    def jump(path, edge, count):
        while path:
            parent, last = path[:-1], path[-1]
            if last == edge:
                count -= 1
                if count == 0:
                    return intervals[parent][1 if edge == "0" else 0]
            path = parent
        raise ValueError("Open control instruction in closed test wrapper")

    graph = []
    for i, (path, op, arg) in enumerate(rows):
        if op == "CI":
            successors = [i + 1]
        elif op == "CD":
            successors = [jump(path, "0", 1), i + 1]
        elif op == "CB":
            successors = [jump(path, "0", arg)]
        elif op == "CC":
            successors = [jump(path, "1", arg)]
        else:
            successors = []
        graph.append((op, arg, successors))
    return graph


def run(graph, a, b):
    initial = [17, 19, 23, 29, 31, a, b, 37, 41]
    regs = list(initial)
    pc = 0
    limit = 16 * (a + b + 1) + 100
    for steps in range(limit):
        op, arg, targets = graph[pc]
        if op == "CH":
            expected = list(initial)
            expected[0] += a == b
            expected[5] = expected[6] = 0
            assert regs == expected, (a, b, regs, expected)
            return steps + 1
        if op == "CI":
            regs[arg] += 1
            pc = targets[0]
        elif op == "CD":
            positive = regs[arg] > 0
            if positive:
                regs[arg] -= 1
            pc = targets[int(positive)]
        else:
            pc = targets[0]
    raise AssertionError(("Step limit", a, b, regs, pc))


def main():
    raw = (HERE / "eq_clean_hits.json").read_bytes()
    trees = json.loads(raw)
    rng = random.Random(219)
    cases = [(a, b) for a in range(41) for b in range(41)]
    cases += [(0, 10000), (10000, 0), (10000, 10000),
              (9999, 10000), (10000, 9999)]
    cases += [(rng.randrange(10001), rng.randrange(10001)) for _ in range(64)]
    results = []
    for i, tree in enumerate(trees):
        graph = compile_cfg([[tree, ["CI", 0]], ["CH", None]])
        steps = [run(graph, a, b) for a, b in cases]
        results.append({"search_hit": i, "cases": len(cases),
                        "source_steps": sum(steps), "maximum_steps": max(steps),
                        "status": "ALL_FINITE_CASES_PASS"})
    result = {"status": "ALL_FINITE_CASES_PASS",
              "scope": "Finite diagnostic only; unbounded hit10 proof is separate",
              "input_sha256": hashlib.sha256(raw).hexdigest(),
              "results": results}
    (HERE / "clean_eq_finite.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
