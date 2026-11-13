#!/usr/bin/env python3
"""Check paths and payload bytes referenced by the frozen 67/94 graph."""
import gzip
import hashlib
import json
from pathlib import Path


def sha(data):
    return hashlib.sha256(data).hexdigest()


root = Path(__file__).resolve().parent
graph = json.loads((root / "polynomial.json").read_bytes())
binding = graph["coefficient_binding"]
for key, digest_key in (("certificate", "certificate_sha256"),
                        ("ordinary_proof", "ordinary_proof_sha256")):
    path = root / binding[key]
    if sha(path.read_bytes()) != binding[digest_key]:
        raise RuntimeError(f"{key} hash mismatch: {path}")
total = 0
for name, metadata in sorted(binding["ports"].items()):
    path = root / binding["path"] / metadata["file"]
    compressed = path.read_bytes()
    raw = gzip.decompress(compressed)
    if (sha(compressed) != metadata["gzip_sha256"] or
            sha(raw) != metadata["raw_sha256"] or
            len(raw) != metadata["raw_bytes"] or
            int.from_bytes(raw, "big").bit_length() != metadata["bits"]):
        raise RuntimeError(f"{name} payload mismatch: {path}")
    total += len(raw)
if total != binding["raw_bytes"]:
    raise RuntimeError("aggregate raw byte count mismatch")
print(json.dumps({"status": "PASS", "ports": len(binding["ports"]),
                  "raw_bytes": total, "scope": "graph metadata paths and payload hashes; no Lean port or PDF proof"},
                 sort_keys=True))
