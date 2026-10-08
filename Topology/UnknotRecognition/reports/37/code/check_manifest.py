#!/usr/bin/env python3
"""Verify shipped file bytes without trusting filenames outside the package."""
import hashlib
from pathlib import Path

root=Path(__file__).resolve().parents[1]
manifest=root/'SHA256SUMS'
failed=[]; count=0
for line in manifest.read_text().splitlines():
    expected,relative=line.split('  ',1)
    path=(root/relative).resolve()
    if root not in path.parents:
        failed.append(relative+': unsafe path'); continue
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=expected:
        failed.append(relative)
    count+=1
if failed:
    raise SystemExit('FAILED: '+', '.join(failed))
print(f'VERIFIED: {count} files (manifest itself excluded).')
