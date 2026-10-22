#!/usr/bin/env python3
"""Read-only checks binding the Rocq prototype to the independent source census.

Usage: python3 audit_macro_component.py REPOSITORY ROCQ_COMPONENT/src
This script checks source identity and interfaces. It does not compile proofs.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path
from audit_macro_footprint import REL, children, parse_edge, parse_program, reachable, strip_comments


def lemma_statements(source: str) -> dict[str, str]:
    return {
        m[2]: re.sub(r"\s+", " ", m[3]).strip()
        for m in re.finditer(r"^(Lemma|Theorem)\s+(\w+)([\s\S]*?)^Proof\.", strip_comments(source), re.M)
        if re.search(r"\bENode\s+\d+\b", m[3])
    }


def dependencies(source: str) -> set[str]:
    result = set()
    for m in re.finditer(r"^From\s+(\S+)\s+Require\s+(?:Import|Export)\s+([^.]*)\.", source, re.M):
        result.update(m[1] + "." + name for name in m[2].split())
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("repository", type=Path)
    parser.add_argument("component_src", type=Path)
    args = parser.parse_args()
    base = args.repository / REL / "rocq/rocq-extension/coq"
    src = args.component_src
    old = (base / "215/ProgLibPerm.v").read_text()
    old_statements = lemma_statements(old)
    roots = {int(n) for statement in old_statements.values() for n in re.findall(r"\bENode\s+(\d+)\b", statement)}
    dag215 = parse_program((base / "215/DagPerm.v").read_text())
    dag217 = parse_program((base / "217/DagDom.v").read_text())
    footprint = reachable(dag215, roots)
    files = sorted((src / "KLocal").glob("*.v"))
    texts = {p.stem: p.read_text() for p in files}
    canonical_rows = re.findall(r"^\s*\|\s*(\d+)\s*=>\s*\(([^,]+),\s*([^\)]+)\)\s*$",
                               strip_comments(texts["MacroProgram"]), re.M)
    canonical = {int(n): [parse_edge(a), parse_edge(b)] for n, a, b in canonical_rows}
    assert set(canonical) == footprint
    assert all(canonical[n] == dag215[n] == dag217[n] for n in canonical)
    assert all(children(canonical, n) <= footprint for n in canonical)
    assert old_statements == lemma_statements(texts["Macro215Contracts"])
    expected = old.replace("From K215F Require Import DagPerm.", "From KLocal Require Import MacroProgram.")
    expected = expected.replace("dagPerm", "macro_prog").replace("dag_nodes", "macro_nodes")
    assert expected == texts["MacroLibrary"]
    # Traverse project dependencies of the 215 contract component, ignoring Coq's stdlib.
    seen, todo = set(), ["KLocal.Macro215Contracts"]
    while todo:
        module = todo.pop()
        if module in seen or module.startswith("Coq."):
            continue
        seen.add(module)
        path = src.joinpath(*module.split(".")).with_suffix(".v")
        assert path.exists(), "unresolved project dependency: " + module
        todo.extend(dependencies(path.read_text()) - seen)
    assert not any(m.startswith("K217F.") for m in seen)
    assert "KLocal.MacroBindings" not in seen
    output = {
        "status": "PASS_INDEPENDENT_SOURCE_REVIEW_NOT_COMPILER_EXECUTION",
        "canonical_node_count": len(canonical), "macro_root_count": len(roots),
        "matching_literal_node_lemma_statements": len(old_statements),
        "canonical_rows_equal_both_original_programs": True,
        "macro_library_is_exact_stated_program_retargeting": True,
        "macro215_project_import_closure": sorted(seen),
        "macro215_imports_no_217_program": True,
        "component_files": {str(p.relative_to(src)): {
            "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
            "bytes": len(p.read_bytes()), "lines": len(p.read_text().splitlines())
        } for p in files},
        "component_total_lines": sum(len(p.read_text().splitlines()) for p in files),
        "component_total_bytes": sum(len(p.read_bytes()) for p in files),
        "limits": [
            "The adapter uses the common MacroLibrary.St record, not the existing nominal ProgLibPerm.St.",
            "The unchanged L2RootPerm client and full endpoint have not been checked by this source audit.",
            "The local macro theorem does not assert equivalence of candidate root 0, which lies outside the footprint.",
            "No overall endpoint source or compilation-time reduction follows from these component metrics."
        ]
    }
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
