#!/usr/bin/env python3
"""Reconstruct the clean equality source from the pinned K220 leaf list.

Standard library only; no search is performed.  This establishes the literal
source replacement and counts.  See report/sections/equality.tex for its mathematical
semantics; a separately validated Turing table is still required.
"""
from pathlib import Path
import argparse
import hashlib
import json

BASELINE_SHA256 = "837e92d7b1c107330f160f654f6c36ff0b03dfbf6bc2b89c6f782eb7db4c4ce7"
D5, D6 = ("CD", 5), ("CD", 6)
I5 = ("CI", 5)
C1, C2, B1 = ("CC", 1), ("CC", 2), ("CB", 1)
F = (I5, (D6, C2))
T = (D6, ((D5, C2), F))
X = (D5, ((D5, C1), B1))
OLD = (T, X)
P = (D6, C2)
U = (P, B1)
A = (D5, U)
L = (A, D6)
Z = (D5, C1)
R = (Z, U)
NEW = (L, R)


def compact(obj):
    return (json.dumps(obj, separators=(",", ":")) + "\n").encode("ascii")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def leaf(tree):
    return isinstance(tree[0], str)


def sites(tree, path=""):
    if leaf(tree):
        return [[path, *tree]]
    return sites(tree[0], path + "0") + sites(tree[1], path + "1")


def parse(rows):
    nodes = {}
    for path, op, arg in rows:
        assert path and set(path) <= {"0", "1"}
        assert path not in nodes
        assert op in {"CI", "CD", "CB", "CC", "CH"}
        nodes[path] = (op, arg)

    def visit(path):
        if path in nodes:
            return nodes[path]
        assert any(p.startswith(path + "0") for p in nodes)
        assert any(p.startswith(path + "1") for p in nodes)
        return visit(path + "0"), visit(path + "1")

    tree = visit("")
    assert sites(tree) == rows
    return tree


def metrics(tree):
    seen = set()

    def visit(node):
        if node in seen:
            return
        seen.add(node)
        if not leaf(node):
            visit(node[0])
            visit(node[1])

    visit(tree)
    rows = sites(tree)
    return {"dag_nodes": len(seen), "leaf_occurrences": len(rows),
            "maximum_depth": max(len(p) for p, _, _ in rows),
            "maximum_zero_run": max(len(z) for p, _, _ in rows
                                    for z in p.split("1"))}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sites220", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    raw = args.sites220.read_bytes()
    assert sha(raw) == BASELINE_SHA256, "Unexpected baseline source hash"
    original = parse(json.loads(raw))
    paths = []

    def replace(node, path=""):
        if node == OLD:
            paths.append(path)
            return NEW
        if leaf(node):
            return node
        return replace(node[0], path + "0"), replace(node[1], path + "1")

    changed = replace(original)
    assert len(paths) == 4
    assert metrics(original) == {"dag_nodes": 208, "leaf_occurrences": 4744,
                                 "maximum_depth": 38, "maximum_zero_run": 6}
    assert metrics(changed) == {"dag_nodes": 206, "leaf_occurrences": 4744,
                                "maximum_depth": 38, "maximum_zero_run": 6}
    output = compact(sites(changed))
    receipt = {"status": "LITERAL_SOURCE_REPLACEMENT_VERIFIED",
               "baseline_source_sha256": sha(raw),
               "source_sha256": sha(output),
               "old_macro_sha256": sha(compact(OLD)),
               "new_macro_sha256": sha(compact(NEW)),
               "replaced_paths": paths,
               "old_metrics": metrics(original),
               "new_metrics": metrics(changed),
               "scope": "Source syntax/counts only; semantics proved separately"}
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "sites.json").write_bytes(output)
    (args.out / "old_equality_macro.json").write_bytes(compact(OLD))
    (args.out / "new_equality_macro.json").write_bytes(compact(NEW))
    (args.out / "source_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
