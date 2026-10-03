#!/usr/bin/env python3
"""Release-author exact manifest writer; not part of read-only verification."""
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from verify_pins import verify_inputs, SOURCE_SHA256
ROOT=Path(__file__).resolve().parent
verify_inputs()
records={}
for path in sorted(ROOT.rglob('*')):
    if path.is_symlink():raise RuntimeError('Symlinks may not be shipped')
    if not path.is_file() or path == ROOT/'manifest.json':continue
    if '__pycache__' in path.parts or path.suffix in ('.pyc','.log','.png','.pdf'):
        raise RuntimeError('Excluded artifact present: '+path.name)
    raw=path.read_bytes()
    records[path.relative_to(ROOT).as_posix()]=dict(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
manifest=dict(package='report18-cellular-clock-domination-portable-reproducibility',date='2026-10-03',source_sha256=SOURCE_SHA256,predecessor_source_sha256='38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a',inventory_policy='Every regular delivered file except manifest.json itself; extra files and symlinks are rejected by verifier',files=records)
(ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Wrote',len(records),'exact file entries')
