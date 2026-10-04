#!/usr/bin/env python3
"""Fresh read-only input inventory. Never imports or executes source code."""
import hashlib
import json
import os
from datetime import datetime, timezone
from pathlib import Path
import stat
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
NAMES = [
    "arity-table-asymptotics-20261004",
    "independent-arity-asymptotics-audit-20261004",
]


def snapshot():
    paths = []
    for name in NAMES:
        base = ROOT / name
        paths.extend([base, *sorted(base.rglob("*"))])
        paths.extend([ROOT / (name + ".zip"), ROOT / (name + "-receipt.json")])
    rows = []
    for p in sorted(paths):
        s = p.lstat()
        row = {"path": str(p), "mode": stat.S_IMODE(s.st_mode),
               "size": s.st_size, "mtime_ns": s.st_mtime_ns,
               "kind": "file" if p.is_file() else "directory"}
        if p.is_symlink():
            raise ValueError("Unexpected symbolic link: " + str(p))
        if p.is_file():
            row["sha256"] = hashlib.sha256(p.read_bytes()).hexdigest()
        elif not p.is_dir():
            raise ValueError("Unexpected filesystem object: " + str(p))
        rows.append(row)
    return {"captured_utc": datetime.now(timezone.utc).isoformat(), "objects": rows}


def main():
    phase = sys.argv[1]
    if phase not in ("before", "after"):
        raise ValueError("phase must be before or after")
    current = snapshot()
    target = HERE / "evidence" / ("input-" + phase + ".json")
    if phase == "after":
        before = json.loads((HERE / "evidence/input-before.json").read_text())
        assert current["objects"] == before["objects"], "Input inventory changed"
        current["unchanged_from_before"] = True
    with target.open("x") as f:
        json.dump(current, f, indent=2)
        f.write("\n")
    print(phase, len(current["objects"]), "objects", current["captured_utc"])


if __name__ == "__main__":
    main()
