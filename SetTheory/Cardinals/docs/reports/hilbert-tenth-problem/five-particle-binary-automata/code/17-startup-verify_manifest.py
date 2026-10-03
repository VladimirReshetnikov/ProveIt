#!/usr/bin/env python3
"""Check exact delivered inventory and bytes; no files are ignored except self-manifest."""
import hashlib
import json
from pathlib import Path, PurePosixPath
ROOT=Path(__file__).resolve().parent
SOURCE_SHA256='fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'

def verify():
    manifest=json.loads((ROOT/'manifest.json').read_text())
    if manifest['source_sha256'] != SOURCE_SHA256:
        raise RuntimeError('Manifest uses wrong source identity')
    records=manifest['files']
    actual=set()
    for path in ROOT.rglob('*'):
        if path.is_symlink():raise RuntimeError('Symlink not permitted: '+path.relative_to(ROOT).as_posix())
        if path.is_file() and path != ROOT/'manifest.json':actual.add(path.relative_to(ROOT).as_posix())
    if actual != set(records):
        raise RuntimeError('Manifest inventory mismatch: missing='+repr(sorted(set(records)-actual))+'; extra='+repr(sorted(actual-set(records))))
    for name,rec in records.items():
        path=PurePosixPath(name)
        if path.is_absolute() or '..' in path.parts or not path.parts or str(path)!=name:
            raise RuntimeError('Unsafe manifest entry')
        data=(ROOT/name).read_bytes()
        if len(data)!=rec['bytes'] or hashlib.sha256(data).hexdigest()!=rec['sha256']:
            raise RuntimeError('Manifest bytes mismatch: '+name)
    if records['source.json']['sha256']!=SOURCE_SHA256:
        raise RuntimeError('Wrong source bytes')
    return len(records)

if __name__=='__main__':
    print('PASS:',verify(),'files match exact manifest inventory and hashes')
