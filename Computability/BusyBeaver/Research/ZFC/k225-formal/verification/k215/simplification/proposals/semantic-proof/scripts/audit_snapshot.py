#!/usr/bin/env python3
"""Compare live K215 source bytes with two archived proof checkpoints.

This is a provenance check, not a proof checker. It neither runs a compiler nor
executes archived code. Archives are read in memory and never extracted.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import tarfile

ROOTS = ("Computability/BusyBeaver/Lean", "Logic/FirstOrder/Lean",
         "SetTheory/ZF/Lean", "SetTheory/BoundedConsistency/Lean")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return digest(path.read_bytes())


def compare(path, expected, name):
    if not path.is_file():
        return {"module": name, "status": "MISSING", "expected_sha256": expected}
    actual = sha(path)
    return {"module": name, "status": "MATCH" if actual == expected else "DIFFERENT",
            "expected_sha256": expected, "actual_sha256": actual}


def summarize(rows):
    return {"counts": {s: sum(r["status"] == s for r in rows)
                       for s in ["MATCH", "DIFFERENT", "MISSING"]}, "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    base = repo / "Computability/BusyBeaver/Research/ZFC/k225-formal"
    coq = base / "rocq/rocq-extension/coq/215"
    audit = base / "verification/k215"
    normalized = json.loads((audit / "rocq/normalized-91/verification.json").read_text())
    normalized_rows = [compare(coq / (name + ".v"), row["source_sha256"], name)
                       for name, row in normalized["compiled"].items()]

    old = audit / "rocq/actual"
    old_index = json.loads((old / "evidence-index.json").read_text())
    old_review = json.loads((old / "actual-review.json").read_text())
    assert sha(old / "evidence.tar.gz") == old_index["archive_sha256"]
    byhash = {r["sha256"]: n for n, r in old_index["members"].items()}
    original_rows = []
    with tarfile.open(old / "evidence.tar.gz") as archive:
        for module, record_hash in old_review["module_record_sha256"].items():
            if not module.startswith("K215F."):
                continue
            data = archive.extractfile(byhash[record_hash]).read()
            assert digest(data) == record_hash
            record = json.loads(data)
            original_rows.append(compare(coq / (module[6:] + ".v"), record["source_sha256"], module))

    lean = audit / "simplification/phase9/lean"
    lean_result = json.loads((lean / "result.json").read_text())
    lean_index = json.loads((lean / "index.json").read_text())
    assert sha(lean / "execution.tar.gz") == lean_result["archive_sha256"]
    with tarfile.open(lean / "execution.tar.gz") as archive:
        data = archive.extractfile("execution/inventory.json").read()
    assert digest(data) == lean_index["execution/inventory.json"]["sha256"]
    lean_rows = []
    for row in json.loads(data)["modules"]:
        paths = [repo / r / (row["module"].replace(".", "/") + ".lean") for r in ROOTS]
        found = [p for p in paths if p.is_file()]
        assert len(found) <= 1
        lean_rows.append(compare(found[0] if found else paths[0], row["source_sha256"], row["module"]))

    candidate = repo / "Computability/BusyBeaver/Research/ZFC/candidate-k215"
    result = {
        "status": "SOURCE_AND_RECEIPT_COMPARISON_ONLY",
        "head": subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip(),
        "lean_vs_phase9_union": summarize(lean_rows),
        "rocq_vs_original_237_source_checkpoint": summarize(original_rows),
        "rocq_vs_normalized_44_local_source_checkpoint": summarize(normalized_rows),
        "live_local_rocq_source_count": len(list(coq.glob("*.v"))),
        "literal_inputs": {n: sha(candidate / n) for n in ["k215.tm", "k215.native.tm", "sites215.json"]},
        "limits": [
            "Comparisons concern source bytes, not live compiled objects or proof validity.",
            "The baseline has 195 reference modules in addition to its 42 local K215 modules.",
            "The phase-nine Lean receipt covers a 197-module union, including five prefix modules outside the endpoint closure.",
            "DIFFERENT does not mean incorrect. It means this particular receipt does not cover these exact source bytes.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "head": result["head"],
                     "lean_phase9": result["lean_vs_phase9_union"]["counts"],
                     "rocq_original": result["rocq_vs_original_237_source_checkpoint"]["counts"],
                     "rocq_normalized": result["rocq_vs_normalized_44_local_source_checkpoint"]["counts"]}, indent=2))


if __name__ == "__main__":
    main()
