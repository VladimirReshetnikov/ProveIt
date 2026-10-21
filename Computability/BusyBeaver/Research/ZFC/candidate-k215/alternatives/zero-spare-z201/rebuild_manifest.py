#!/usr/bin/env python3
"""Maintainer helper: rebuild the packet inventory after intentional edits.
Running this is not verification and is not needed to verify the release.
"""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
files={}
for path in sorted(ROOT.rglob('*')):
    if path.is_symlink():
        raise RuntimeError('Cannot seal a symlink: '+str(path.relative_to(ROOT)))
    if path.is_file() and '__pycache__' not in path.relative_to(ROOT).parts:
        name=path.relative_to(ROOT).as_posix()
        if name!='manifest.json':
            files[name]=hashlib.sha256(path.read_bytes()).hexdigest()
(ROOT/'manifest.json').write_text(json.dumps(dict(schema=1,algorithm='SHA-256',files=files),indent=2)+'\n')
print('Recorded',len(files),'files')
