#!/usr/bin/env python3
"""Verify the pinned proposal corpus hashes; this is not a novelty proof."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("--manifest", type=Path,
                        default=Path(__file__).resolve().parent.parent /
                        "audit" / "proposal_text_manifest.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    repo = args.repo.resolve()
    head = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"],
                          check=True, text=True, capture_output=True).stdout.strip()
    failures = []
    if head != manifest["commit"]:
        failures.append("HEAD differs from the pinned commit")
    base = repo / "Analysis/GeneralizedRiemannHypothesis/docs/proposals"
    total_bytes = 0
    directories = set()
    for entry in manifest["files"]:
        path = base / entry["path"]
        try:
            data = path.read_bytes()
        except OSError as error:
            failures.append(f"{entry['path']}: {error}")
            continue
        total_bytes += len(data)
        directories.add(Path(entry["path"]).parts[0])
        actual_blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        if len(data) != entry["bytes"]:
            failures.append(f"{entry['path']}: size differs")
        if hashlib.sha256(data).hexdigest() != entry["sha256"]:
            failures.append(f"{entry['path']}: SHA-256 differs")
        if actual_blob != entry["git_blob"]:
            failures.append(f"{entry['path']}: Git blob differs")
    result = {"ok": not failures, "audit_kind": "proposal_corpus_integrity",
              "proof_validation": False, "novelty_validation": False,
              "expected_commit": manifest["commit"], "actual_commit": head,
              "files_checked": len(manifest["files"]),
              "directories_checked": len(directories),
              "bytes_checked": total_bytes, "failures": failures}
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
