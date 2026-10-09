#!/usr/bin/env python3
"""Verify every shipped file against the artifact manifest (read-only).

Extra files from a local rebuild or rerun are permitted. Missing, changed,
non-regular or symlinked shipped files fail verification.
"""
import hashlib
import json
from pathlib import Path, PurePosixPath


ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest = json.loads((ROOT / "ARTIFACT_MANIFEST.json").read_text())
    problems = []
    for item in manifest["files"]:
        name = PurePosixPath(item["path"])
        if name.is_absolute() or ".." in name.parts:
            problems.append(item["path"] + ": invalid path")
            continue
        path = ROOT / name
        if not path.is_file() or path.is_symlink():
            problems.append(item["path"] + ": missing or non-regular")
            continue
        data = path.read_bytes()
        if len(data) != item["bytes"] or hashlib.sha256(data).hexdigest() != item["sha256"]:
            problems.append(item["path"] + ": digest mismatch")
    print(json.dumps(dict(status="PASS" if not problems else "FAIL",
                          files_checked=len(manifest["files"]),
                          problems=problems), indent=2))
    return bool(problems)


if __name__ == "__main__":
    raise SystemExit(main())
