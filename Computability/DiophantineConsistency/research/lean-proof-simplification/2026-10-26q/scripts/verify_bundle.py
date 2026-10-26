#!/usr/bin/env python3
"""Verify final archive members after extraction; does not run Lean."""
import hashlib
from pathlib import Path
root = Path(__file__).resolve().parent.parent
entries = (root/'SHA256SUMS').read_text().splitlines()
for line in entries:
    expected, rel = line.split('  ', 1)
    p = root / rel
    if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != expected:
        raise SystemExit('Checksum mismatch: '+rel)
print(f'Verified {len(entries)} file checksums.')
