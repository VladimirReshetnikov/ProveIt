#!/usr/bin/env python3
"""Report exact expanded AST properties of an inherited-spelling grammar."""
import argparse
from functools import cache
import json
from pathlib import Path


def properties(package, path):
    source = json.loads((package / "inputs/closed-sequence-grammar-next22.json").read_text())
    symbols = json.loads((package / "inputs/semantic-symbols.json").read_text())
    lines = (package / "inputs/semantic.txt").read_text().splitlines()
    count = int(lines[0].split()[0])
    old = {w: (w[:int(k)], w[int(k):]) for k, w, q in map(str.split, lines[1:count + 1])}
    names = {int(q): w for k, w, q in map(str.split, lines[1:count + 1])}
    by_ast = {int(i): names[int(q)] for q, i in source["sequence_ast_roots"].items()}
    data = json.loads(path.read_text())
    grammar = {w: (a, b) for w, a, b in data["rules"]}
    @cache
    def ast(i):
        if i in by_ast:
            return word(by_ast[i])
        row = source["ast_dag"][i]
        return ("L", tuple(row[1])) if row[0] == "L" else ("N", ast(row[1]), ast(row[2]))
    @cache
    def word(w):
        if len(w) == 1:
            return ast(source["atoms"][symbols[w]]["ast"])
        return ("N", *(word(c) for c in grammar.get(w, old.get(w))))
    @cache
    def prop(tree):
        if tree[0] == "L":
            return 0, 0, 0, 0, 0
        a, b = prop(tree[1]), prop(tree[2])
        return 1 + a[0], max(1 + a[0], a[1], b[1]), 1 + max(a[2], b[2]), a[3] + b[3] + int(1 + a[0] > 5), a[4] + b[4] + int(1 + a[0] > 6)
    tree = ast(source["original_ast"])
    result = prop(tree)
    bad = []
    leaves = 0
    def walk(t, p):
        nonlocal leaves
        if t[0] == "L":
            leaves += 1
            run = max(map(len, p.split("1")))
            if run > 6 and len(bad) < 3:
                bad.append({"path": p, "instruction": t[1], "zero_run": run})
        else:
            walk(t[1], p + "0")
            walk(t[2], p + "1")
    walk(tree, "")
    return {"status": "PASS_EXACT_AST_MEASUREMENT", "rules_count": len(grammar), "leading_zeros": result[0],
            "maximum_zero_run": result[1], "maximum_leaf_depth": result[2], "nodes_with_lead_above_5": result[3],
            "nodes_with_lead_above_6": result[4], "instruction_leaves": leaves, "example_zero6_failures": bad,
            "scope": "Finite exact AST measurement, not a machine theorem."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("grammar", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = properties(args.package, args.grammar)
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
