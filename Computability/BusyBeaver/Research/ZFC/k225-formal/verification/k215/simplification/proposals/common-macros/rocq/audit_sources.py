#!/usr/bin/env python3
"""Compare the checked prototype against its pinned ProveIt source files."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile

PIN = "6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95"
ZFC = "Computability/BusyBeaver/Research/ZFC/k225-formal"
COPIES = {
    "K230/RM.v": ZFC + "/verification/k215/simplification/proposals/zfc215-simplification/source_proof/deps/K230/RM.v",
    "K230S/KCode230.v": ZFC + "/verification/k215/simplification/proposals/semantic-coverage/rocq/source/K230S/KCode230.v",
    "K230L/Codes230.v": ZFC + "/verification/k215/simplification/proposals/proof-contracts/rocq/reference/K230L/Codes230.v",
    "K215F/DagPerm.v": ZFC + "/rocq/rocq-extension/coq/215/DagPerm.v",
    "K217F/DagDom.v": ZFC + "/rocq/rocq-extension/coq/217/DagDom.v",
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def rows(text):
    return {int(n): body for n, body in
            re.findall(r"\| (\d+) => (\([^\n]+\))", text)}


def declarations(text):
    return {m.group(1): m.group(0).removesuffix("Proof.").strip()
            for m in re.finditer(r"(?m)^Lemma\s+(\w+)\b([\s\S]*?)Proof\.", text)
            if re.search(r"ENode \d+", m.group(0))}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("repo", type=Path)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    repo = args.repo.resolve()
    result = {"repository_commit": PIN, "copies": [], "checks": {}}
    for local, source in COPIES.items():
        upstream = (repo / source).read_bytes()
        actual = (root / "src" / local).read_bytes()
        assert upstream == actual, local
        result["copies"].append({"local": "src/" + local, "source": source,
                                 "sha256": sha(actual), "exact_copy": True})
    original_path = ZFC + "/rocq/rocq-extension/coq/215/ProgLibPerm.v"
    original = (repo / original_path).read_text()
    expected = original.replace("From K215F Require Import DagPerm.",
        "From KLocal Require Import MacroProgram.").replace(
        "dagPerm", "macro_prog").replace("dag_nodes", "macro_nodes")
    assert expected == (root / "src/KLocal/MacroLibrary.v").read_text()
    result["library"] = {"source": original_path,
        "source_sha256": sha((repo / original_path).read_bytes()),
        "derived_sha256": sha(expected.encode()), "proof_changes":
        ["import DagPerm becomes import MacroProgram", "dagPerm becomes macro_prog",
         "dag_nodes becomes macro_nodes"], "lines": len(original.splitlines())}
    old_decls = declarations(original)
    new_decls = declarations((root / "src/KLocal/Macro215Contracts.v").read_text())
    assert old_decls == new_decls
    assert len(old_decls) == 58
    roots = sorted(set(map(int, re.findall(r"ENode (\d+)", original))))
    assert len(roots) == 53
    target = rows((root / "src/K215F/DagPerm.v").read_text())
    previous = rows((root / "src/K217F/DagDom.v").read_text())
    footprint = set(roots)
    todo = roots[:]
    while todo:
        n = todo.pop()
        for child in map(int, re.findall(r"ENode (\d+)", target[n])):
            if child not in footprint:
                footprint.add(child)
                todo.append(child)
    canonical = rows((root / "src/KLocal/MacroProgram.v").read_text())
    assert len(footprint) == 89 and set(canonical) == footprint
    assert all(canonical[n] == target[n] == previous[n] for n in footprint)
    result["checks"] = {"exact_textual_contract_signatures": 58,
        "distinct_macro_roots": roots, "canonical_footprint": sorted(footprint),
        "footprint_count": 89, "canonical_cells_equal_both_candidates": True,
        "claim": "textual signatures share a new St; not yet a drop-in nominal-type audit"}
    reference_identity = []
    archive_path = ZFC + "/verification/k215/rocq/actual/evidence.tar.gz"
    with tarfile.open(repo / archive_path, "r:gz") as archive:
        for ns, name in [("K230", "RM"), ("K230L", "Codes230"), ("K230S", "KCode230")]:
            member = f"attempts/{ns}.{name}/run1/{name}.v"
            recorded = archive.extractfile(member).read()
            actual = (root / "src" / ns / (name + ".v")).read_bytes()
            assert recorded.replace(b"\r\n", b"\n") == actual
            reference_identity.append({"module": ns + "." + name,
                "recorded_member": member, "recorded_sha256": sha(recorded),
                "actual_sha256": sha(actual), "changes": "CRLF to LF only"})
    result["reference_identity"] = reference_identity
    result["status"] = "PASS"
    (root / "evidence").mkdir(exist_ok=True)
    (root / "evidence/source-audit.json").write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: 58 textual contracts, 53 roots, 89 closed cells; reference definitions match.")


if __name__ == "__main__":
    main()
