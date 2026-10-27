#!/usr/bin/env python3
"""Check every sealed deliverable byte; newly generated replay files are ignored."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def main():
    entries=json.loads((ROOT/'MANIFEST.sha256.json').read_text())['files']
    for row in entries:
        relative=Path(row['path'])
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError('Unsafe manifest path')
        target=ROOT/relative
        if not target.is_file():
            raise ValueError('Missing file: '+str(relative))
        raw=target.read_bytes()
        if len(raw)!=row['bytes'] or hashlib.sha256(raw).hexdigest()!=row['sha256']:
            raise ValueError('Hash mismatch: '+str(relative))
    print(json.dumps({'status':'PASS','files_checked':len(entries)}))


if __name__=='__main__':
    main()
