"""Check final artifact SHA-256 hashes and independent baseline Git blob hashes."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    for entry in manifest["files"]:
        path = ROOT / entry["path"]
        data = path.read_bytes()
        if len(data) != entry["size_bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise SystemExit(f"Artifact mismatch: {entry['path']}")
    baseline = json.loads((ROOT / "provenance" / "baseline_manifest.json").read_text())
    prefix = "Topology/UnknotRecognition/fast/"
    for entry in baseline["files"]:
        relative = entry["repository_path"].removeprefix(prefix)
        data = (ROOT / "reference" / "fast" / relative).read_bytes()
        blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        if (len(data) != entry["size_bytes"] or blob != entry["git_blob"]
                or hashlib.sha256(data).hexdigest() != entry["sha256"]):
            raise SystemExit(f"Baseline mismatch: {relative}")
    print(f"Verified {len(manifest['files'])} artifact hashes and "
          f"{len(baseline['files'])} exact baseline Git blobs.")


if __name__ == "__main__":
    main()
