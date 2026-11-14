#!/usr/bin/env python3
"""Verify release bytes only; mathematical check commands are in README.txt."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
entries=json.loads((root/'manifest_sha256.json').read_text())['sha256']
for path,expected in entries.items():
 actual=hashlib.sha256((root/path).read_bytes()).hexdigest()
 if actual!=expected:raise SystemExit('Hash mismatch: '+path)
print('Verified '+str(len(entries))+' release files.')
