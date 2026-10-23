#!/usr/bin/env python3
"""Read-only census of the pinned K215 Rocq macro reuse opportunity."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

BASE = "Computability/BusyBeaver/Research/ZFC/k225-formal"
PIN = "cbf94cb552a3b49509e0eee80e7455d4eb5974c6"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_nodes(path: Path) -> dict[int, tuple[str, str]]:
    rows = re.findall(r"^  \| (\d+) => \(([^,]+), ([^)]+)\)$", path.read_text(), re.M)
    result = {int(n): (a, b) for n, a, b in rows}
    if not result or sorted(result) != list(range(len(result))):
        raise ValueError(f"Incomplete literal node parser: {path}")
    for pair in result.values():
        for edge in pair:
            if re.fullmatch(r"E(?:Node|Inc|Decnz|Break|Continue) \d+|EHalt", edge) is None:
                raise ValueError(f"Unexpected edge: {edge!r}")
    return result


def footprint(root: int, nodes: dict[int, tuple[str, str]]) -> set[int]:
    seen, pending = set(), [root]
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        for edge in nodes[node]:
            if edge.startswith("ENode "):
                pending.append(int(edge.split()[1]))
    return seen


def remove_comments(text: str) -> str:
    # Rocq comments can nest. Do not use a non-greedy regex for this check.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                out.append(" ")
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Rocq comment")
    return "".join(out)


def normalized(text: str) -> str:
    text = remove_comments(text)
    for old, new in (("K215F", "K218F"), ("dagPerm", "dag219"), ("DagPerm", "Dag219")):
        text = re.sub(r"\b" + old + r"\b", new, text)
    return " ".join(text.split())


def audit(repo: Path) -> dict:
    coq = repo / BASE / "rocq/rocq-extension/coq"
    old_path, new_path = coq / "218/Dag219.v", coq / "215/DagPerm.v"
    old, new = parse_nodes(old_path), parse_nodes(new_path)
    old_lib, new_lib = coq / "218/ProgLib219.v", coq / "215/ProgLibPerm.v"
    text = new_lib.read_text()
    lemmas = []
    for match in re.finditer(r"^(?:Lemma|Theorem) (\w+).*?\nProof\..*?\bQed\.", text, re.M | re.S):
        declaration = match.group(0).split("\nProof.", 1)[0]
        root = re.search(r"sem \(ENode (\d+)\)", declaration)
        if root:
            n = int(root.group(1))
            reach = footprint(n, old)
            lemmas.append({"name": match.group(1), "root": n,
                           "start_line": text[:match.start()].count("\n") + 1,
                           "lines": len(match.group(0).splitlines()),
                           "table_agreement_on_reachable_nodes": all(old[j] == new.get(j) for j in reach)})
    roots = sorted({x["root"] for x in lemmas})
    common = set().union(*(footprint(n, old) for n in roots))
    if not lemmas or not all(x["table_agreement_on_reachable_nodes"] for x in lemmas):
        raise ValueError("Claimed common macro does not have an unchanged footprint")
    if len(common) != 89 or len(roots) != 53 or len(lemmas) != 58:
        raise ValueError("Baseline census changed; review rather than silently updating claims")
    if not normalized(old_lib.read_text()) == normalized(new_lib.read_text()):
        raise ValueError("Macro libraries no longer match under namespace/program renaming")
    receipt = json.loads((repo / BASE / "verification/k215/rocq/normalized-91/verification.json").read_text())
    mismatches = []
    for name, record in receipt["compiled"].items():
        path = coq / "215" / (name + ".v")
        current = digest(path) if path.exists() else None
        if current != record["source_sha256"]:
            mismatches.append({"name": name, "receipt_sha256": record["source_sha256"],
                               "current_sha256": current})
    duplicates = []
    for name in ("Runtime230Core.v", "Interpreter230Sites.v", "Sim230.v", "Tape230Blocks.v", "Tape230Carry.v"):
        copies = sorted(coq.glob("*/" + name))
        duplicates.append({"name": name, "copies": len(copies),
                           "aggregate_bytes": sum(p.stat().st_size for p in copies),
                           "k215_bytes": (coq / "215" / name).stat().st_size})
    return {
        "status": "PASS_STATIC_CENSUS", "baseline_commit": PIN,
        "scope": "Literal table/static source census; does not compile or certify a machine endpoint",
        "input_hashes": {str(p.relative_to(repo)): digest(p) for p in (old_path, new_path, old_lib, new_lib)},
        "old_program_nodes": len(old), "new_program_nodes": len(new),
        "changed_existing_nodes": [n for n in old if old[n] != new.get(n)],
        "added_nodes": sorted(set(new) - set(old)),
        "concrete_macro_lemmas": len(lemmas), "distinct_macro_roots": len(roots),
        "closed_footprint_size": len(common), "macro_roots": roots,
        "closed_footprint": sorted(common), "macro_lemmas": lemmas,
        "macro_libraries_identical_under_declared_renaming": True,
        "old_macro_library_bytes": old_lib.stat().st_size,
        "new_macro_library_bytes": new_lib.stat().st_size,
        "new_macro_library_lines": len(text.splitlines()),
        "concrete_macro_lemma_lines": sum(x["lines"] for x in lemmas),
        "current_k215_local_v_files": len(list((coq / "215").glob("*.v"))),
        "historical_normalized91_module_count": len(receipt["compiled"]),
        "historical_normalized91_mismatches": mismatches,
        "historical_normalized91_top_times_seconds": sorted(
            [{"module": k, "seconds": v["seconds"]} for k, v in receipt["compiled"].items()],
            key=lambda row: row["seconds"], reverse=True)[:12],
        "runtime_source_copies": duplicates,
        "caution": "Footprint transport reuses existing mathematical proofs. Deleting a duplicate variant does not imply the selected K215 transitive closure shrinks. Historical timing and receipt hashes are not a fresh current-tree build."
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.repo.resolve())
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "concrete_macro_lemmas", "distinct_macro_roots", "closed_footprint_size")}))


if __name__ == "__main__":
    main()
