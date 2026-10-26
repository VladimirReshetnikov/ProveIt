#!/usr/bin/env python3
"""Recompute source counts using the pinned Git objects, not working-tree files."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

if len(sys.argv) != 2:
    raise SystemExit("Usage: source_metrics.py /path/to/ProveIt")
repo = Path(sys.argv[1]).resolve()
bundle = Path(__file__).resolve().parents[1]
expected = json.loads((bundle / "evidence/source_metrics.json").read_text())
pin = expected["repository_commit"]
old_total = new_total = 0
for row in expected["files"]:
    path = row["path"]
    if row["old_lines"]:
        old = subprocess.check_output(["git", "-C", str(repo), "show", f"{pin}:{path}"])
        assert hashlib.sha256(old).hexdigest() == row["old_sha256"], path
    else:
        old = b""
    new = (bundle / "proposed" / path).read_bytes()
    assert hashlib.sha256(new).hexdigest() == row["new_sha256"], path
    old_lines = len(old.splitlines())
    new_lines = len(new.splitlines())
    assert (old_lines, new_lines) == (row["old_lines"], row["new_lines"]), path
    old_total += old_lines
    new_total += new_lines
    print(f"{Path(path).name}: {old_lines} -> {new_lines}")
print(f"Total: {old_total} -> {new_total}; saving {old_total - new_total} lines.")
assert old_total - new_total == expected["lines_saved"]
