"""Verify the delivered SHA-256 manifest before regeneration."""
from pathlib import Path
import hashlib

root = Path(__file__).resolve().parent
entries = (root / "MANIFEST.sha256").read_text().splitlines()
for line in entries:
    expected, filename = line.split("  ", 1)
    observed = hashlib.sha256((root / filename).read_bytes()).hexdigest()
    if observed != expected:
        raise SystemExit("Hash mismatch: " + filename)
print("Verified", len(entries), "files.")
