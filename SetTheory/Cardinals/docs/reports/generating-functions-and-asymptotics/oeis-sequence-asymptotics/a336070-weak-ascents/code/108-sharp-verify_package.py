#!/usr/bin/env python3
"""Verify the sealed article/check payload. Correctness gates survive python -O."""
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import sys

ROOT = Path(__file__).resolve().parent
TOP = ('README.md', 'report108.tex', 'report108.pdf', 'assemble.py', 'build.sh',
       'verify_package.py', 'seal.py', 'replay.py')

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def payload_paths(root=ROOT):
    files = [root/name for name in TOP]
    files += sorted((root/'source').glob('*.tex'))
    for p in sorted((root/'checks').rglob('*')):
        if p.is_file() and '__pycache__' not in p.parts and not any(x.startswith(('mutation-', 'replay-')) for x in p.relative_to(root/'checks').parts):
            if p.parent == root/'checks' and (p.suffix in ('.py', '.json') or p.name == 'README.md'):
                files.append(p)
            elif p.parent in (root/'checks'/'logs',root/'checks'/'weak_logs') and p.suffix in ('.stdout', '.stderr', '.json'):
                files.append(p)
    for p in sorted((root/'validation').glob('*')):
        if p.is_file() and p.suffix in ('.json', '.txt', '.md'):
            files.append(p)
    return sorted(files, key=lambda p: p.relative_to(root).as_posix())

def verify(root=ROOT):
    doc = json.loads((root/'manifest.json').read_text())
    require(doc.get('schema') == 'report108-sha256-v1', 'Unrecognized manifest schema')
    rows = doc.get('files')
    require(isinstance(rows, list) and rows, 'Empty or invalid manifest')
    names = [r['path'] for r in rows]
    require(names == sorted(set(names)), 'Manifest paths must be unique and sorted')
    actual = [p.relative_to(root).as_posix() for p in payload_paths(root)]
    require(names == actual, 'Manifest payload membership mismatch')
    for row in rows:
        name = row['path']; rel = PurePosixPath(name)
        require(not rel.is_absolute() and '..' not in rel.parts and str(rel) == name, 'Unsafe manifest path')
        p = root/name
        require(p.is_file() and not p.is_symlink(), f'Missing or symlinked payload: {name}')
        data = p.read_bytes()
        require(len(data) == row['bytes'], f'Byte count mismatch: {name}')
        require(sha256(data).hexdigest() == row['sha256'], f'SHA256 mismatch: {name}')
    require((root/'report108.pdf').read_bytes().startswith(b'%PDF-'), 'Final PDF missing its header')
    print(json.dumps({'status': 'passed', 'payload_files': len(rows), 'pdf_sha256': sha256((root/'report108.pdf').read_bytes()).hexdigest()}, sort_keys=True))
    return doc

if __name__ == '__main__':
    try:
        verify()
    except Exception as exc:
        print(json.dumps({'status': 'failed', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        sys.exit(1)
