"""Check the delivered files; does not import or execute a proof checker."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parent
checked = 0
for line in (root / "MANIFEST.sha256").read_text().splitlines():
    expected, name = line.split("  ", 1)
    path = root / name
    if not path.is_file():
        raise SystemExit("Missing file: " + name)
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit("Hash mismatch: " + name)
    checked += 1
print("Verified", checked, "files")
