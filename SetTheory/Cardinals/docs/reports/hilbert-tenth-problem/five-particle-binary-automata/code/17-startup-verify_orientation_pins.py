#!/usr/bin/env python3
"""Authenticate the separately audited proof-only addendum, not prove its theorem."""
import hashlib
import json
from pathlib import Path
from verify_pins import verify_inputs, SOURCE_SHA256
ROOT=Path(__file__).resolve().parent
verify_inputs()
ADDENDUM=ROOT/'orientation-addendum'
manifest=json.loads((ADDENDUM/'first-encounter-manifest.json').read_text())
if manifest['source_sha256'] != SOURCE_SHA256 or set(manifest['files']) != {'FIRST_ENCOUNTER_OPTIMALITY.md','first-encounter-independent-audit.md'}:
    raise RuntimeError('Wrong orientation-addendum manifest scope')
for name, record in manifest['files'].items():
    raw=(ADDENDUM/name).read_bytes()
    if len(raw)!=record['bytes'] or hashlib.sha256(raw).hexdigest()!=record['sha256']:
        raise RuntimeError('Sealed addendum mismatch: '+name)
receipt=dict(status='PIN_MATCH',scope='The two proof notes and their sealed producer manifest match mandatory known SHA-256 pins. This is artifact authentication, not an executable proof of orientation optimality. The independent mathematical audit and its finite arithmetic checks are inherited evidence; no new literal-source or CA execution is claimed.',source_sha256=SOURCE_SHA256,producer_manifest_sha256=hashlib.sha256((ADDENDUM/'first-encounter-manifest.json').read_bytes()).hexdigest(),proof_files=manifest['files'])
(ADDENDUM/'pin-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
