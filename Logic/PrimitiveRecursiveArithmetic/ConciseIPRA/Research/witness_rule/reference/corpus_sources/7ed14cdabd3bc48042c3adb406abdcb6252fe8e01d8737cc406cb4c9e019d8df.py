"""Verify exactly the distributed payload before regenerating any outputs."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
manifest = json.loads((root / "MANIFEST.json").read_text())
for entry in manifest["files"]:
    path = root / entry["path"]
    data = path.read_bytes()
    if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
        raise SystemExit("Payload mismatch: " + entry["path"])
print("PASS: " + str(len(manifest["files"])) + " payload files verified.")
