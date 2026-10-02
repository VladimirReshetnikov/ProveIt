#!/usr/bin/env python3
"""Bind packaged proof sources to the independent reviewers' source records."""
from pathlib import Path
import hashlib
r=Path(__file__).resolve().parents[1]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
lower=(r/'audit/lower-input-sha256.txt').read_text().split('  ',1)[0]
assert digest(r/'proofs/normalized-kernel-lower.md')==lower,'Changed lower proof after independent audit'
for line in (r/'audit/proof-sha256.txt').read_text().splitlines():
    expected,name=line.split('  ',1)
    basename=Path(name).name
    p=r/'audit'/basename
    assert digest(p)==expected,basename
    if basename=='one-sided-next-constant-proof.md':
        assert digest(r/'proofs/coefficient-upper.md')==expected,'Changed upper proof after independent audit'
for line in (r/'audit/audited-proof-sha256.txt').read_text().splitlines():
    expected,name=line.split('  ',1)
    assert digest(r/name)==expected,name
print('PASS: packaged upper/lower sources match independent audit input hashes')
