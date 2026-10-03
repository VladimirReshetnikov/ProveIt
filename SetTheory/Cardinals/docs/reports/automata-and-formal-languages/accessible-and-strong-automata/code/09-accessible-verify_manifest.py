"""Verify all shipped files listed in the package checksum manifest."""
from pathlib import Path
import hashlib
root = Path(__file__).resolve().parent.parent
lines = (root / "MANIFEST.sha256").read_text().splitlines()
for line in lines:
    digest, name = line.split("  ", 1)
    p = root / name
    assert p.resolve().is_relative_to(root.resolve()), name
    assert p.is_file() and not p.is_symlink(), name
    assert hashlib.sha256(p.read_bytes()).hexdigest() == digest, name
print(f"PASS: {len(lines)} shipped files match MANIFEST.sha256")
