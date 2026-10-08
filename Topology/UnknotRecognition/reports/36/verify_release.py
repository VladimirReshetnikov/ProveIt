"""Verify every regular file listed in the release SHA-256 manifest."""
import hashlib
from pathlib import Path
root = Path(__file__).resolve().parent
count = 0
for line in (root / "SHA256SUMS").read_text().splitlines():
    expected, name = line.split("  ", 1)
    relative = Path(name)
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit("Unsafe manifest path: " + name)
    path = root / relative
    if not path.is_file() or path.is_symlink():
        raise SystemExit("Missing or nonregular file: " + name)
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit("SHA-256 mismatch: " + name)
    count += 1
print("PASS: verified", count, "release files")
