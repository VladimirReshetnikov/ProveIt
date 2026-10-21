#!/usr/bin/env python3
"""Check the finite source transport underlying the exact 216-state candidate.

Usage:
  python audit_source210.py SOURCE205 SOURCE202 SOURCE210 SOURCE_LANGUAGE_PY OUTPUT_JSON

SOURCE_LANGUAGE_PY is the vendored source_language.py with tree validation,
closure bounds, and two separately implemented control-flow resolvers.
The numerical-calculus and arithmetic-macro theorems remain separate
mathematical dependencies; this program verifies the finite source transport.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


EXPECTED_HASHES = (
    "07f18539b63fee7e22f2f19a517ddfd43d99e440ea7b62a64c4a0978a6bfd258",
    "abb7229877759170b61dfcfe21ca0889b3df2f91f4215383817a125eb0f8996c",
    "8b5dc46f10d927b2db5e4bcb522d482779ec61c72c82717d7bf12fca3550a3bc",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source205", type=Path)
    parser.add_argument("source202", type=Path)
    parser.add_argument("source210", type=Path)
    parser.add_argument("source_language_py", type=Path)
    parser.add_argument("output_json", type=Path)
    args = parser.parse_args()
    paths = (args.source205, args.source202, args.source210)
    for path, expected in zip(paths, EXPECTED_HASHES):
        require(sha(path) == expected, f"Unexpected source bytes: {path}")

    module_spec = importlib.util.spec_from_file_location(
        "audited_source_language", args.source_language_py)
    require(module_spec is not None and module_spec.loader is not None,
            "Cannot load source-language helper")
    source = importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(source)

    reference, base, candidate = (json.loads(path.read_text()) for path in paths)
    reference_tree = source.tree(reference)
    base_tree = source.tree(base)
    candidate_tree = source.tree(candidate)
    require([row[1:] for row in reference] == [row[1:] for row in base],
            "Reference and rebracketing have different primitive words")
    reference_cfg = source.graph_arithmetic(reference)[0]
    base_cfg = source.graph_arithmetic(base)[0]
    require(reference_cfg == base_cfg, "Reference and rebracketing CFGs differ")
    require(source.graph_intervals(reference) == reference_cfg,
            "Reference CFG resolvers disagree")
    require(source.graph_intervals(base) == base_cfg,
            "Rebracketed CFG resolvers disagree")

    body_paths = ("111", "110101", "110100101")
    permutation = (2, 1, 0)

    def at(tree, path):
        for bit in path:
            require(not source.leaf(tree), "Body path extends past a leaf")
            tree = tree[int(bit)]
        return tree

    bodies = [at(base_tree, path) for path in body_paths]
    for path, index in zip(body_paths, permutation):
        require(at(candidate_tree, path) == bodies[index], "Changed command body")

    def permuted(tree, path=""):
        if path in body_paths:
            return bodies[permutation[body_paths.index(path)]]
        if source.leaf(tree):
            return tree
        return permuted(tree[0], path + "0"), permuted(tree[1], path + "1")

    require(permuted(base_tree) == candidate_tree, "Changed source outside the three bodies")
    boundaries = [source.boundary(body) for body in bodies]
    require(all(break_depth == continue_depth == 0
                for break_depth, continue_depth, halts in boundaries),
            "A moved body has an escaping break or continuation")
    require(source.graph_arithmetic(candidate)[0] == source.graph_intervals(candidate),
            "Final source CFG resolvers disagree")

    body_receipts = []
    for name, body, old_path, new_path in zip(
            ("MP", "DROP", "NIP"), bodies, body_paths, reversed(body_paths)):
        rows = source.sites(body)
        require(source.graph_arithmetic(rows)[0] == source.graph_intervals(rows),
                f"Internal CFG resolvers disagree for {name}")
        body_receipts.append({
            "name": name,
            "old_path": old_path,
            "new_path": new_path,
            "primitive_occurrences": len(rows),
            "boundary": source.boundary(body),
            "literal_subtree_preserved": True,
        })

    expected_metrics = {"dag_nodes": 202, "leaf_occurrences": 4751,
                        "maximum_depth": 44, "maximum_zero_run": 6}
    require(source.metrics(candidate_tree) == expected_metrics, "Unexpected final source metrics")
    require(source.metrics(reference_tree)["dag_nodes"] == 205, "Wrong reference DAG size")
    require(source.metrics(base_tree) == expected_metrics, "Wrong rebracketed source metrics")
    output = {
        "status": "PASS",
        "reference_sha256": sha(args.source205),
        "noncommon202_sha256": sha(args.source202),
        "source210_sha256": sha(args.source210),
        "source_language_sha256": sha(args.source_language_py),
        "auditor_sha256": sha(Path(__file__)),
        "source210_metrics": expected_metrics,
        "noncommon202_matches_reference_primitive_word": True,
        "noncommon202_matches_reference_complete_guarded_ordinal_CFG": True,
        "tag_permutation": list(permutation),
        "body_receipts": body_receipts,
        "exterior_source_identical": True,
        "source210_independent_CFG_resolvers_agree": True,
        "semantic_scope": (
            "Transport of inherited noncommon-input command contracts by a wire-tag "
            "bijection. Arithmetic macro contracts and numerical-calculus equiconsistency "
            "are separate inherited mathematical dependencies."
        ),
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
