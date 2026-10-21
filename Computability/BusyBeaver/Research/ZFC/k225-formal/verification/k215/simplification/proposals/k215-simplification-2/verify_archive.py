#!/usr/bin/env python3
"""Verify the delivered packet byte-for-byte; this is not a proof checker."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent
record=json.loads((root/'MANIFEST.sha256.json').read_text())
errors=[]
for name,expected in record['files'].items():
 p=root/name
 if not p.is_file():errors.append('MISSING '+name);continue
 actual=hashlib.sha256(p.read_bytes()).hexdigest()
 if actual!=expected:errors.append('MISMATCH '+name)
if errors:
 print('\n'.join(errors));sys.exit(1)
print('ARCHIVE_MANIFEST_PASS',len(record['files']),'files')
print('These hashes bind the delivered files. Use the subpacket build helpers for fresh kernel checks.')
