#!/usr/bin/env python3
"""Build the integration diff after verifying the supplied baseline source blobs."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def git_blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True,
                        help="fast/ directory from the pinned baseline commit")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "patches" / "fast_symbolic_compression.patch")
    arguments = parser.parse_args()
    manifest = json.loads((ROOT / "provenance" / "source_manifest.json").read_text())
    entries = {r["path"]: r for r in manifest["files"] if r["prefix"] == "fast"}
    for relative, record in entries.items():
        path = arguments.baseline / relative
        if git_blob(path.read_bytes()) != record["sha"]:
            raise SystemExit(f"Baseline blob mismatch: {relative}")
    proposed = ROOT / "implementation" / "fast"
    files = {p.relative_to(proposed).as_posix() for p in proposed.rglob("*")
             if p.is_file() and "__pycache__" not in p.parts and p.suffix != ".pyc"
             and "results" not in p.relative_to(proposed).parts}
    parts = []
    changed = []
    for relative in sorted(set(entries) | files):
        before = (arguments.baseline / relative).read_text() if relative in entries else ""
        after = (proposed / relative).read_text() if relative in files else ""
        if before == after:
            continue
        name = "Topology/UnknotRecognition/fast/" + relative
        parts.append("".join(difflib.unified_diff(
            before.splitlines(keepends=True), after.splitlines(keepends=True),
            fromfile="a/" + name if relative in entries else "/dev/null",
            tofile="b/" + name if relative in files else "/dev/null")))
        changed.append(relative)
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text("".join(parts))
    print(json.dumps({"baseline_source_files_verified": len(entries),
                      "changed_files": changed, "patch": str(arguments.output)}, indent=2))


if __name__ == "__main__":
    main()
