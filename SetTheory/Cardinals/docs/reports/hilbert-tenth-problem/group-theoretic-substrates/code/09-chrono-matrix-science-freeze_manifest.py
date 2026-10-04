#!/usr/bin/env python3
"""Freeze the author packet; external audit output is deliberately separate."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
names = ['ARCHITECTURE.md','SOURCE_NOTES.md','build_certificate.py','check_semantics.py',
         'freeze_manifest.py','review/PACKING_REVIEW.md']
names += [str(p.relative_to(ROOT)) for p in sorted((ROOT/'sources').iterdir()) if p.is_file()]
names += ['evidence/polynomial-dag.json','evidence/build-receipt.json',
          'evidence/coefficients.json','evidence/semantic-checks.json']
rows = []
for name in names:
    raw = (ROOT/name).read_bytes()
    rows.append(dict(path=name,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
manifest = dict(schema='chronological-certificate-freeze-v1',date='2026-10-04',
                status='Complete author source/proof packet; independent mathematics PASS; separate source audit',
                inherited_theorems='Pinned constructive Pell POWER/Sub and upstream fixed-program matrix equivalences',
                files=rows)
(ROOT/'evidence/frozen-manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
print(json.dumps(manifest,sort_keys=True,indent=2))
