"""Verify all delivered-file SHA-256 hashes without executing certificates."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parent
count = 0
for line in (root / "MANIFEST.sha256").read_text().splitlines():
    expected, name = line.split("  ", 1)
    data = (root / name).read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise SystemExit("Hash mismatch: " + name)
    count += 1
print("Verified", count, "file hashes.")
