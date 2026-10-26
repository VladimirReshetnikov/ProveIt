#!/usr/bin/env python3
"""Read-only source pin, file-hash and patch-applicability checks."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
if len(sys.argv) != 2:
    raise SystemExit('Usage: python3 verify_sources.py /path/to/ProveIt')
repo = Path(sys.argv[1]).resolve()
manifest = json.loads((ROOT / 'audit/source_bindings.json').read_text())
pin = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
if pin != manifest['source_commit']:
    raise SystemExit(f'Wrong source revision: {pin}')
for item in manifest['files']:
    p = repo / item['path']
    if not p.is_file():
        raise SystemExit(f'Missing source file: {item["path"]}')
    if hashlib.sha256(p.read_bytes()).hexdigest() != item['sha256']:
        raise SystemExit(f'Modified source file: {item["path"]}')
for patch in sorted((ROOT / 'patches').glob('*.patch')):
    subprocess.run(['git', 'apply', '--check', str(patch)], cwd=repo, check=True)
print(f'Pinned source, {len(manifest["files"])} file hashes, and all patches match.')
print('No Lean production compilation was performed by this script.')
