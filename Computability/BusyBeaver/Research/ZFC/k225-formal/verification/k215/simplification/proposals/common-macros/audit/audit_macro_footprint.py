#!/usr/bin/env python3
"""Independent finite census for the Dom/Perm common Rocq macro footprint.

This is a source-data audit, not a proof-assistant theorem.  It parses the
literal Rocq program tables and compares them with the source JSON, computes
the greatest closed region on which the tables agree, and finds the smaller
dependency closure required by the library's literal-node lemma statements.
No repository producer or proof script is executed.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import subprocess
from pathlib import Path

PIN = "6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95"
REL = Path("Computability/BusyBeaver/Research/ZFC/k225-formal")


def strip_comments(source: str) -> str:
    """Handle nested Rocq comments rather than silently accepting a regex cut."""
    out, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith("(*", i):
            depth += 1
            i += 2
        elif source.startswith("*)", i):
            assert depth > 0, "unbalanced close comment"
            depth -= 1
            i += 2
        else:
            if depth == 0 or source[i] == "\n":
                out.append(source[i])
            i += 1
    assert depth == 0, "unclosed comment"
    return "".join(out)


def normalized_library(source: str) -> str:
    source = strip_comments(source)
    for old, new in [("K215F", "KCandidate"), ("K217F", "KCandidate"),
                     ("DagPerm", "DagCandidate"), ("DagDom", "DagCandidate"),
                     ("dagPerm", "dagCandidate"), ("dagDom", "dagCandidate")]:
        source = re.sub(r"\b" + old + r"\b", new, source)
    return re.sub(r"\s+", " ", source).strip()


def parse_edge(s: str) -> list:
    m = re.fullmatch(r"(ENode|EInc|EDecnz|EBreak|EContinue)\s+(\d+)", s.strip())
    if m:
        names = {"ENode": "N", "EInc": "EInc", "EDecnz": "EDecnz", "EBreak": "EBreak", "EContinue": "EContinue"}
        return [names[m[1]], int(m[2])]
    assert s.strip() == "EHalt", s
    return ["EHalt", None]


def parse_program(source: str) -> dict[int, list]:
    source = strip_comments(source)
    rows = re.findall(r"^\s*\|\s*(\d+)\s*=>\s*\(([^,]+),\s*([^\)]+)\)\s*$", source, re.M)
    result = {int(n): [parse_edge(a), parse_edge(b)] for n, a, b in rows}
    assert len(result) == len(rows), "duplicate rows"
    assert re.search(r"\|\s*_\s*=>\s*\(EHalt, EHalt\)", source), "unexpected default"
    size = int(re.search(r"mkProg\s+dag_nodes\s+0\s+(\d+)\.", source)[1])
    assert set(result) == set(range(size)), "not a complete literal table"
    return result


def children(nodes: dict[int, list], n: int) -> set[int]:
    return {v for kind, v in nodes[n] if kind == "N"}


def greatest_agreeing_region(a: dict[int, list], b: dict[int, list]) -> set[int]:
    region = {n for n in a.keys() & b.keys() if a[n] == b[n]}
    while True:
        smaller = {n for n in region if children(a, n) <= region}
        if smaller == region:
            return region
        region = smaller


def reachable(nodes: dict[int, list], roots: set[int]) -> set[int]:
    result, todo = set(roots), list(roots)
    while todo:
        n = todo.pop()
        for m in children(nodes, n) - result:
            result.add(m)
            todo.append(m)
    return result


def validates(a: dict[int, list], b: dict[int, list], region: set[int]) -> bool:
    return all(n in a and n in b and a[n] == b[n] and children(a, n) <= region for n in region)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("repository", type=Path)
    args = parser.parse_args()
    repo = args.repository.resolve()
    base = repo / REL
    inputs = {
        "dom_table": base / "rocq/rocq-extension/coq/217/DagDom.v",
        "perm_table": base / "rocq/rocq-extension/coq/215/DagPerm.v",
        "dom_library": base / "rocq/rocq-extension/coq/217/ProgLibDom.v",
        "perm_library": base / "rocq/rocq-extension/coq/215/ProgLibPerm.v",
        "dom_json": base / "lean217/dagdom_nodes.json",
        "perm_json": base / "lean215/dagperm_nodes.json",
    }
    texts = {key: path.read_text() for key, path in inputs.items()}
    a, b = parse_program(texts["dom_table"]), parse_program(texts["perm_table"])
    for prefix, nodes in [("dom", a), ("perm", b)]:
        data = json.loads(texts[prefix + "_json"])
        assert nodes == {int(k): v for k, v in data["nodes"].items()}, "Rocq/JSON mismatch"
        assert len(nodes) == data["nnodes"]
    common_a = normalized_library(texts["dom_library"])
    common_b = normalized_library(texts["perm_library"])
    assert common_a == common_b, "library code is not a candidate rename"

    lemmas = []
    for m in re.finditer(r"^(Lemma|Theorem)\s+(\w+)([\s\S]*?)^Proof\.", strip_comments(texts["perm_library"]), re.M):
        nodes = sorted({int(n) for n in re.findall(r"\bENode\s+(\d+)\b", m[3])})
        if nodes:
            lemmas.append({"name": m[2], "nodes": nodes})
    roots = {n for lemma in lemmas for n in lemma["nodes"]}
    closed = greatest_agreeing_region(a, b)
    footprint = reachable(a, roots)
    assert footprint <= closed and validates(a, b, footprint)

    # Deliberate source mutations test the finite audit's failure boundary.
    changed = copy.deepcopy(b)
    changed[188][0] = ["EInc", 8]
    assert not validates(a, changed, footprint)
    omitted = footprint - {188}
    assert not validates(a, b, omitted)
    irrelevant = copy.deepcopy(b)
    irrelevant[0] = [["EHalt", None], ["EHalt", None]]
    assert validates(a, irrelevant, footprint)

    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    output = {
        "status": "PASS_SOURCE_DATA_AUDIT_NOT_KERNEL_PROOF",
        "expected_pin": PIN, "observed_commit": head, "pin_matches": head == PIN,
        "inputs": {key: {"path": str(path.relative_to(repo)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                         "bytes": len(path.read_bytes()), "lines": len(texts[key].splitlines())}
                   for key, path in inputs.items()},
        "library_bodies_equal_after_comment_candidate_name_whitespace_normalization": True,
        "normalized_library_sha256": hashlib.sha256(common_a.encode()).hexdigest(),
        "source_nodes": len(a), "target_nodes": len(b),
        "changed_shared_nodes": sorted(n for n in a.keys() & b.keys() if a[n] != b[n]),
        "new_target_nodes": sorted(b.keys() - a.keys()),
        "greatest_closed_agreeing_region_count": len(closed),
        "excluded_source_nodes": sorted(a.keys() - closed),
        "literal_node_macro_lemma_count": len(lemmas), "literal_macro_root_count": len(roots),
        "macro_footprint_count": len(footprint), "macro_footprint": sorted(footprint),
        "macro_lemmas": lemmas,
        "negative_checks": {"changed_macro_effect_rejected": True, "missing_child_rejected": True},
        "scope_check": {"root_change_outside_footprint_allowed": True},
        "limitation": "Checks source tables and dependencies only. Transport and endpoint claims require kernel checking."
    }
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
