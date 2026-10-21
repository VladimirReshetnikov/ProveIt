#!/usr/bin/env python3
"""Verify package bytes only. Does not import or execute research programs."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
m=json.loads((R/'MANIFEST.json').read_text())
def check(p,digest,size=None):
    rel=Path(p);assert not rel.is_absolute() and '..' not in rel.parts,p
    b=(R/rel).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,p
    if size is not None:assert len(b)==size,p
for x in m['files']:check(x['path'],x['sha256'],x['bytes'])
for line in (R/'SHA256SUMS').read_text().splitlines():
    digest,p=line.split('  ',1);check(p,digest)
print('PASS:',len(m['files']),'payload files; manifest and SHA256SUMS agree.')
print('This is byte-integrity verification, not a new machine correctness proof.')
