"""Check the archive's frozen SHA-256 ledger before regenerating evidence."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parent
failures = []
count = 0
for line in (ROOT / "MANIFEST.sha256").read_text().splitlines():
    expected, name = line.split("  ", 1)
    path = ROOT / name
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        failures.append(name)
    count += 1
if failures:
    raise SystemExit("Hash mismatch: " + ", ".join(failures))
print(f"Verified {count} files.")
