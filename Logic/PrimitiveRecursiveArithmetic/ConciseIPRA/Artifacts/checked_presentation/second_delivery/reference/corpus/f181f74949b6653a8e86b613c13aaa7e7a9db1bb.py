"""Verify the original archive payload; run before regenerating receipts."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
failed = []
checked = 0
for line in (ROOT/"MANIFEST.sha256").read_text().splitlines():
    if not line:
        continue
    expected, name = line.split("  ", 1)
    path = ROOT/name
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        failed.append(name)
    checked += 1
print(json.dumps(dict(files_checked=checked, failures=failed), indent=2))
if failed:
    raise SystemExit(1)

