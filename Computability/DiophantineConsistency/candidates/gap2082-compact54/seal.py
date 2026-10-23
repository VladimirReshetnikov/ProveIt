#!/usr/bin/env python3
"""Refresh the candidate's deterministic full-tree manifest after deliberate edits."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
records = {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
           for p in sorted(ROOT.rglob('*')) if p.is_file() and p.name!='MANIFEST.json'
           and '__pycache__' not in p.parts and p.suffix!='.pyc'}
(ROOT/'MANIFEST.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'sealed_files':len(records)},indent=2))
