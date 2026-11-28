#!/usr/bin/env python3
"""Verify pinned source bytes without modifying the supplied Git checkout.

Reads Git objects at the recorded revision, so the worktree may be at another
revision and may contain unrelated local changes. No network is used.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path, help="Existing ProveIt Git checkout")
    args = parser.parse_args()
    artifacts = Path(__file__).resolve().parent.parent / "artifacts"
    failures = []
    total = 0
    for manifest_name in ("source_manifest.json", "proposal_text_manifest.json"):
        manifest = json.loads((artifacts / manifest_name).read_text())
        commit = manifest["commit"]
        for entry in manifest["files"]:
            path = entry["path"]
            try:
                content = subprocess.check_output(
                    ["git", "-C", str(args.repo), "show", f"{commit}:{path}"],
                    stderr=subprocess.PIPE,
                )
            except subprocess.CalledProcessError as exc:
                failures.append(f"Cannot read {commit}:{path}: {exc.stderr.decode().strip()}")
                continue
            actual = hashlib.sha256(content).hexdigest()
            if actual != entry["sha256"]:
                failures.append(f"SHA-256 mismatch: {path}")
            if len(content.decode("utf-8").splitlines()) != entry["lines"]:
                failures.append(f"Line-count mismatch: {path}")
            total += 1
        print(f"{manifest_name}: {len(manifest['files'])} entries checked at {commit}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"PASS: all {total} source and proposal file hashes and line counts match.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
