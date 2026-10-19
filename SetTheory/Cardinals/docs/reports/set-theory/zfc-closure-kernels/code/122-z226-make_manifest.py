#!/usr/bin/env python3
"""Refresh the archive's byte manifest after intentional artifact changes.

Run reproduce.py to check an existing release; this script creates a new
manifest and is not itself verification of file integrity.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
EXCLUDE = {'manifest.json','report.aux','report.log','report.out','report.toc',
           'report.fdb_latexmk','report.fls','report.synctex.gz'}


def main():
    files = {}
    for p in sorted(ROOT.rglob('*')):
        relative = p.relative_to(ROOT)
        if not p.is_file() or str(relative) in EXCLUDE or '__pycache__' in relative.parts:
            continue
        if any(part.startswith('replay-') for part in relative.parts):
            continue
        files[relative.as_posix()] = hashlib.sha256(p.read_bytes()).hexdigest()
    data = dict(format='proveit-k226-artifact-manifest-v1', files=files,
                note='SHA-256 byte inventory, not a proof. manifest.json excludes itself and LaTeX build intermediates.')
    (ROOT/'manifest.json').write_text(json.dumps(data,indent=2)+'\n')
    print('Manifest files:', len(files))


if __name__ == '__main__':
    main()
