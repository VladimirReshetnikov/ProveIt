#!/usr/bin/env python3
"""Read-only integrity, source-size, and optional ProveIt patch checks."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, help="Unmodified ProveIt checkout with reviewed target bytes")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "MANIFEST.json").read_text())
    errors = []
    for row in manifest["files"]:
        path = root / row["path"]
        if not path.is_file():
            errors.append("Missing: " + row["path"])
        elif path.stat().st_size != row["size_bytes"] or sha256(path) != row["sha256"]:
            errors.append("Hash/size mismatch: " + row["path"])
    metrics = json.loads((root / "evidence/combined_metrics.json").read_text())
    for row in metrics["targets"]:
        for side in ["before", "after"]:
            p = root / ("overlays/production-" + side) / row["path"]
            actual = len(p.read_text().splitlines())
            if actual != row[side + "_lines"]:
                errors.append("Line-count mismatch: " + side + " " + row["path"])
    old = sum(row["before_lines"] for row in metrics["targets"])
    new = sum(row["after_lines"] for row in metrics["targets"])
    if (old, new, old - new) != (609, 565, 44):
        errors.append("Combined metrics differ from 609 -> 565 (44 saved)")
    checked_patches = []
    if args.repo:
        repo = args.repo.resolve()
        for row in metrics["targets"]:
            original = root / "overlays/production-before" / row["path"]
            current = repo / row["path"]
            if not current.is_file() or sha256(current) != sha256(original):
                errors.append("Repository target differs from reviewed baseline: " + row["path"])
        for patch in sorted((root / "patches").glob("*.patch")):
            result = subprocess.run(["git", "apply", "--check", str(patch)],
                                    cwd=repo, text=True, capture_output=True)
            checked_patches.append({"patch": patch.name, "exit_code": result.returncode})
            if result.returncode:
                errors.append("Patch check failed: " + patch.name + "\n" + result.stderr)
    print(json.dumps({"ok": not errors, "hashed_files": len(manifest["files"]),
                      "target_files": len(metrics["targets"]),
                      "before_lines": old, "after_lines": new,
                      "net_lines_saved": old - new,
                      "patch_checks": checked_patches, "errors": errors}, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
