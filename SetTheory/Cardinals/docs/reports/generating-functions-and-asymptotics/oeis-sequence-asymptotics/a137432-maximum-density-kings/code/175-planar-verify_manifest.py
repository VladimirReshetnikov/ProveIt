#!/usr/bin/env python3
"""Verify all packaged files and reject missing, added, symlinked, or modified files."""
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT=Path(__file__).resolve().parent

def verify(root=ROOT):
    manifest_path=root/'SHA256SUMS.json'
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise ValueError('manifest is not a regular file')
    manifest=json.loads(manifest_path.read_text())
    if not isinstance(manifest,dict) or not manifest:
        raise ValueError('manifest must be a nonempty object')
    for name,digest in manifest.items():
        p=Path(name)
        if not isinstance(name,str) or not name or '\x00' in name or '\\' in name or p.is_absolute() or '..' in p.parts or p.as_posix()!=name:
            raise ValueError('unsafe manifest path')
        if not isinstance(digest,str) or re.fullmatch('[0-9a-f]{64}',digest) is None:
            raise ValueError('invalid digest')
    found={}
    for path in sorted(root.rglob('*')):
        if path.is_symlink() or not (path.is_dir() or path.is_file()):
            raise ValueError('nonregular package entry')
        if path.is_file() and path!=manifest_path:
            found[path.relative_to(root).as_posix()]=hashlib.sha256(path.read_bytes()).hexdigest()
    if found!=manifest:
        raise ValueError('manifest file set or hashes differ')
    return {'status':'PASS','files_checked':len(found)}

if __name__=='__main__':
    sys.dont_write_bytecode=True
    try:
        print(json.dumps(verify(),sort_keys=True))
    except (ValueError,OSError,TypeError) as exc:
        print(str(exc),file=sys.stderr);sys.exit(1)
