"""Verify the delivered research bundle's file sizes and SHA256 hashes."""
from hashlib import sha256
import json
from pathlib import Path
import sys


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "MANIFEST.json").read_text())
    failures = []
    for name, expected in manifest["files"].items():
        path = (root / name).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            failures.append([name, "missing or invalid path"])
            continue
        data = path.read_bytes()
        if len(data) != expected["bytes"] or sha256(data).hexdigest() != expected["sha256"]:
            failures.append([name, "size or digest mismatch"])
    print(json.dumps({"files_checked": len(manifest["files"]), "failures": failures}, indent=2))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
