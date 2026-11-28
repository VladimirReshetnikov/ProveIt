#!/usr/bin/env python3
"""Verify the source/proposal snapshot used by this report.

Default: read pinned objects from a ProveIt Git checkout, without changing it.
Use --working-tree for an exported source tree or to verify checked-out bytes.
This validates byte identity, not the mathematical correctness of the sources.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--working-tree", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "audit/source_manifest.json").read_text())
    audit = json.loads((root / "audit/source_audit.json").read_text())
    failures = []
    contents = {}
    for item in manifest["files"]:
        path = item["path"]
        try:
            if args.working_tree:
                raw = (args.checkout / path).read_bytes()
            else:
                raw = subprocess.run(
                    ["git", "-C", str(args.checkout), "cat-file", "blob",
                     f'{manifest["commit"]}:{path}'],
                    check=True, capture_output=True).stdout
            checks = {
                "size_bytes": len(raw),
                "sha256": hashlib.sha256(raw).hexdigest(),
                "git_blob_sha1": hashlib.sha1(
                    b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest(),
            }
            for key, value in checks.items():
                if item[key] != value:
                    failures.append({"path": path, "check": key,
                                     "expected": item[key], "actual": value})
            contents[path] = raw
        except (OSError, subprocess.CalledProcessError) as exc:
            failures.append({"path": path, "error": str(exc)})
    # Count the published source windows as inclusive physical line ranges.
    totals = {}
    for kind in ("primary", "contingent_helpers"):
        total = 0
        for item in audit[kind]:
            path = audit["source_root"] + "/" + item["path"]
            if path not in contents:
                failures.append({"path": path, "error": "audit source unavailable"})
                continue
            lines = contents[path].decode("utf-8").splitlines()
            count = 0
            for span in item["regions"]:
                n = span["end"] - span["start"] + 1
                if not (1 <= span["start"] <= span["end"] <= len(lines)):
                    failures.append({"path": path, "error": "invalid audit range"})
                if n != span["physical_lines"]:
                    failures.append({"path": path, "error": "range count mismatch"})
                count += n
            if count != item["total_affected_lines"]:
                failures.append({"path": path, "error": "file affected count mismatch"})
            total += count
        totals[kind] = total
    if totals["primary"] != audit["primary_gross_lines"]:
        failures.append({"error": "primary gross total mismatch"})
    if totals["contingent_helpers"] != audit["contingent_gross_lines"]:
        failures.append({"error": "contingent gross total mismatch"})
    result = {
        "status": "FAIL" if failures else "PASS",
        "repository": manifest["repository"], "commit": manifest["commit"],
        "mode": "working_tree" if args.working_tree else "pinned_git_objects",
        "files_checked": len(manifest["files"]),
        "proposal_directories": len(manifest["proposal_directories"]),
        "primary_gross_lines": totals["primary"],
        "contingent_gross_lines": totals["contingent_helpers"],
        "failures": failures,
        "scope": "Byte hashes and range counts; not proof verification or a dependency graph.",
    }
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")
    return bool(failures)


if __name__ == "__main__":
    sys.exit(main())
