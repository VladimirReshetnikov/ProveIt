#!/usr/bin/env python3
"""Verify all delivered files against the SHA-256 manifest."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def main():
    manifest = json.loads((ROOT/'MANIFEST.sha256.json').read_text())
    failures=[]
    for name, expected in manifest['files'].items():
        path=ROOT/name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=expected:
            failures.append(name)
    if failures:
        raise RuntimeError('Missing or changed deliverables: '+', '.join(failures))
    print(json.dumps({'status':'PASS','verified_files':len(manifest['files'])}))


if __name__ == '__main__':
    main()
