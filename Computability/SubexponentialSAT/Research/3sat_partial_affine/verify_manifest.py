#!/usr/bin/env python3
"""Verify all listed deliverables against the supplied SHA-256 manifest."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def main():
    ledger = json.loads((ROOT / "MANIFEST.sha256.json").read_text())
    failures = []
    for item in ledger["files"]:
        relative = Path(item["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise RuntimeError("Unsafe path in manifest")
        path = ROOT / relative
        if not path.is_file():
            failures.append(item["path"] + ": missing")
            continue
        data = path.read_bytes()
        if len(data) != item["bytes"] or hashlib.sha256(data).hexdigest() != item["sha256"]:
            failures.append(item["path"] + ": checksum mismatch")
    if failures:
        raise SystemExit("\n".join(failures))
    print("PASS: " + str(len(ledger["files"])) + " manifest entries verified.")


if __name__ == "__main__":
    main()
