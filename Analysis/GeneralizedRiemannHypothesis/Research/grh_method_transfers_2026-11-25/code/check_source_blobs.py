#!/usr/bin/env python3
"""Verify supplied source bytes, or a full separately obtained checkout."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", type=Path, help="Full checkout of the pinned upstream repository")
    args = ap.parse_args()
    if args.source:
        base = args.source
        entries = json.loads((ROOT / "evidence/upstream_inventory.json").read_text())
    else:
        base = ROOT / "evidence/upstream"
        entries = json.loads((ROOT / "results/source_audit.json").read_text())["included_source_blobs"]
    failures = []
    for ent in entries:
        p = base / ent["path"]
        if not p.is_file():
            failures.append({"path": ent["path"], "error": "missing"})
            continue
        b = p.read_bytes()
        actual = hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
        if actual != ent["sha1"]:
            failures.append({"path": ent["path"], "error": "hash mismatch"})
    print(json.dumps({"checked": len(entries), "failures": failures,
                      "status": "FAIL" if failures else "PASS"}, indent=2))
    raise SystemExit(bool(failures))


if __name__ == "__main__":
    main()
