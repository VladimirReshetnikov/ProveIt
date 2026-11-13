#!/usr/bin/env python3
"""Verify the exact structural shared-terminal transformation, without execution.

Usage: python3 verify_composition.py OFFSET472.py COMPACT468.py

The checked identities support the universal argument in independent_review.txt.
They are not by themselves a proof of the inherited arithmetic bridge.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path


def structural(node):
    return ast.dump(node, include_attributes=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("offset472", type=Path)
    parser.add_argument("compact468", type=Path)
    args = parser.parse_args()
    old_raw, new_raw = args.offset472.read_bytes(), args.compact468.read_bytes()
    old, new = ast.parse(old_raw), ast.parse(new_raw)
    a, b = old.body[1].value, new.body[1].value
    old_head, old_loop = a.body.values
    new_loop = b.body
    old_leaf, old_continuation = old_loop.elt.values
    new_leaf, new_continuation = new_loop.elt.values
    checks = {
        "both_kernels_are_lambdas": isinstance(a, ast.Lambda) and isinstance(b, ast.Lambda),
        "lambda_parameters_identical": structural(a.args) == structural(b.args),
        "all_other_module_statements_identical": all(structural(x) == structural(y)
            for j, (x, y) in enumerate(zip(old.body, new.body)) if j != 1)
            and len(old.body) == len(new.body),
        "packet_generator_identical": len(old_loop.generators) == len(new_loop.generators) == 1
            and structural(old_loop.generators[0]) == structural(new_loop.generators[0]),
        "kernel_binding_identical": isinstance(old.body[1], ast.Assign)
            and isinstance(new.body[1], ast.Assign)
            and [structural(x) for x in old.body[1].targets] == [structural(x) for x in new.body[1].targets],
        "terminal_control_structure": isinstance(a.body, ast.BoolOp)
            and isinstance(a.body.op, ast.Or)
            and isinstance(old_loop, ast.ListComp) and isinstance(new_loop, ast.ListComp)
            and isinstance(old_loop.elt, ast.BoolOp) and isinstance(old_loop.elt.op, ast.Or)
            and isinstance(new_loop.elt, ast.BoolOp) and isinstance(new_loop.elt.op, ast.Or),
        "nonterminal_continuation_identical": structural(old_continuation) == structural(new_continuation),
        "eager_validating_opener_identical": structural(old_head.left) == structural(new_leaf.left),
        "generated_computation_identical": structural(old_leaf.comparators[0]) == structural(new_leaf.comparators[0].right.elts[0]),
        "hypothesis_context_identical": structural(old_head.comparators[0]) == structural(new_leaf.comparators[0].left),
        "old_computation_compares_raw_goal": isinstance(old_leaf.left, ast.Name) and old_leaf.left.id == "a",
        "new_membership_operator": len(new_leaf.ops) == 1 and isinstance(new_leaf.ops[0], ast.In),
        "new_temporary_context_is_pure_list_addition": isinstance(new_leaf.comparators[0], ast.BinOp)
            and isinstance(new_leaf.comparators[0].op, ast.Add)
            and isinstance(new_leaf.comparators[0].right, ast.List)
            and len(new_leaf.comparators[0].right.elts) == 1,
    }
    result = {
        "checks": checks,
        "all_checks_pass": all(checks.values()),
        "old_source_sha256": hashlib.sha256(old_raw).hexdigest(),
        "new_source_sha256": hashlib.sha256(new_raw).hexdigest(),
        "sources_executed": False,
    }
    print(json.dumps(result, indent=2))
    return 0 if result["all_checks_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
