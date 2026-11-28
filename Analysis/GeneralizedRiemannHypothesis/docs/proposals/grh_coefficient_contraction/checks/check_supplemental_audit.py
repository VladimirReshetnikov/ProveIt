#!/usr/bin/env python3
"""Check supplemental proposal text hashes from Git objects without checkout changes.

The repository must contain the recorded supplemental commit. This is an
integrity check, not validation of mathematics, novelty, or Lean builds.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    manifest = json.loads((root / "audit/supplemental_update_manifest.json").read_text())
    base = json.loads((root / "audit/proposal_text_manifest.json").read_text())
    commit = manifest["supplemental_cutoff_commit"]
    prefix = "Analysis/GeneralizedRiemannHypothesis/docs/proposals/"
    failures = []
    checked = 0
    total_bytes = 0
    for entry in [*base["files"], *manifest["files"]]:
        proc = subprocess.run(["git", "-C", str(args.repo.resolve()), "show",
                               f"{commit}:{prefix}{entry['path']}"],
                              capture_output=True)
        if proc.returncode:
            failures.append(f"Cannot read {entry['path']} from {commit}")
            continue
        data = proc.stdout
        checked += 1
        total_bytes += len(data)
        blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"] or blob != entry["git_blob"]:
            failures.append(f"Size or hash mismatch: {entry['path']}")
    aux = "Analysis/GeneralizedRiemannHypothesis/Lean/grh/src/New/Determinant/AuxiliaryForms"
    proc = subprocess.run(["git", "-C", str(args.repo.resolve()), "diff", "--name-only",
                           base["commit"], commit, "--", aux],
                          capture_output=True, text=True)
    if proc.returncode or proc.stdout.strip():
        failures.append("Could not confirm unchanged AuxiliaryForms sources")
    result = {"ok": not failures, "audit_kind": "supplemental_snapshot_integrity",
              "proof_validation": False, "novelty_validation": False,
              "core_commit": base["commit"], "supplemental_commit": commit,
              "principal_texts": len(base["files"]),
              "supplemental_texts": len(manifest["files"]),
              "files_checked": checked, "bytes_checked": total_bytes,
              "auxiliary_forms_unchanged": proc.returncode == 0 and not proc.stdout.strip(),
              "failures": failures}
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
