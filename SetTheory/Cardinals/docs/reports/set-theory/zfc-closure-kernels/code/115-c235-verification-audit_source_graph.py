#!/usr/bin/env python3
"""Independent source-tree graph comparison by trie intervals.

This checker does not import the discovery/compiler/source checkers. It
proves equality of the ordered register actions and both decrement edges,
under the documented structured-register break/continue semantics.
It does not establish the literal TM's runtime simulation.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def graph(data):
    assert isinstance(data, list) and data
    ordered = sorted(data)
    assert ordered == data, "source rows must already be lexicographically ordered"
    leaves = {}
    children = {}
    for index, row in enumerate(data):
        assert len(row) == 3
        path, op, arg = row
        assert isinstance(path, str) and path and set(path) <= {"0", "1"}
        assert len(path) <= 64
        assert path not in leaves
        leaves[path] = index
        for k in range(len(path)):
            parent = path[:k]
            children.setdefault(parent, set()).add(path[k])
        assert op in ("CI", "CD", "CB", "CC", "CH")
        if op in ("CI", "CD"):
            assert type(arg) is int and 0 <= arg < 9
        elif op in ("CB", "CC"):
            assert type(arg) is int and arg >= 1
        else:
            assert arg is None
    assert not set(leaves).intersection(children)
    assert all(edges == {"0", "1"} for edges in children.values())
    assert len(children) == len(leaves) - 1
    intervals = {}
    def visit(node):
        if node in leaves:
            result = leaves[node], leaves[node] + 1
        else:
            a, b = visit(node + "0"), visit(node + "1")
            assert a[1] == b[0]
            result = a[0], b[1]
        intervals[node] = result
        return result
    assert visit("") == (0, len(data))
    def unwind(path, kind, level):
        # A break skips the subtree reached through the selected left edge.
        # A continue restarts the subtree reached through the selected right edge.
        while path:
            edge = path[-1]
            path = path[:-1]
            if edge == kind:
                level -= 1
                if level == 0:
                    if kind == "0":
                        return intervals[path][1] % len(data)
                    return intervals[path][0]
        return 0
    result = []
    for index, (path, op, arg) in enumerate(data):
        after = (index + 1) % len(data)
        if op == "CI":
            effect, targets = ["increment", arg], [after]
        elif op == "CD":
            effect, targets = ["decrement", arg], [unwind(path, "0", 1), after]
        elif op == "CB":
            effect, targets = ["identity"], [unwind(path, "0", arg)]
        elif op == "CC":
            effect, targets = ["identity"], [unwind(path, "1", arg)]
        else:
            effect, targets = ["halt"], []
        result.append([effect, targets])
    return result, {"leaves": len(leaves), "guarded_cases": sum(2 if r[1] == "CD" else 1 for r in data),
                    "maximum_leaf_depth": max(map(len, leaves)), "complete_binary_tree": True}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("baseline", type=Path)
    p.add_argument("candidate", type=Path)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    before_bytes, after_bytes = a.baseline.read_bytes(), a.candidate.read_bytes()
    before, bmeta = graph(json.loads(before_bytes))
    after, ameta = graph(json.loads(after_bytes))
    assert before == after, "guarded operational graph differs"
    common = (json.dumps(before, separators=(",", ":")) + "\n").encode()
    receipt = {"status": "PASS_IDENTICAL_GUARDED_OPERATIONAL_GRAPH", "baseline": bmeta, "candidate": ameta,
               "baseline_sha256": hashlib.sha256(before_bytes).hexdigest(),
               "candidate_sha256": hashlib.sha256(after_bytes).hexdigest(),
               "common_graph_sha256": hashlib.sha256(common).hexdigest(),
               "independent_checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "scope": "All register files; complete source control graph; no literal TM simulation claim"}
    a.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
