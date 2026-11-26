"""Check pinned Git object identities of the cited Lean source in a checkout."""
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
root = Path(sys.argv[1])
hashes = json.loads((HERE/"upstream_blobs.json").read_text())
for name, expected in hashes.items():
    data = (root/name).read_bytes()
    digest = hashlib.sha1(b"blob "+str(len(data)).encode()+b"\x00"+data).hexdigest()
    if digest != expected:
        raise SystemExit(f"Source mismatch at {name}")
print(f"Matched {len(hashes)} pinned source blobs.")
