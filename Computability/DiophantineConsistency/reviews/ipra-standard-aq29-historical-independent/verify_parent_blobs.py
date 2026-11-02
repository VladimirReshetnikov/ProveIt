#!/usr/bin/env python3
"""Check historical parent manifest hashes against the pinned Git commit.

This does not rehash the frozen snapshot or validate the project proof.
"""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[4]
MANIFEST = Path('/tmp/ipra-aq29-fresh-source-closure-v2/manifest.json')
EXPECTED_MANIFEST = '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
EXPECTED_COMMIT = '74f797792c2ef3f81bc9d9e8eb14a58664a3aded'

raw = MANIFEST.read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED_MANIFEST
manifest = json.loads(raw)
assert manifest['head'] == EXPECTED_COMMIT
assert manifest['project_modules'] == len(manifest['sources']) == 1210
rows = {}
for name, row in manifest['sources'].items():
    path = row['workspace_path']
    parts = Path(path)
    assert not parts.is_absolute() and '..' not in parts.parts
    assert '\n' not in path and '\r' not in path and path not in rows
    rows[path] = row['sha256']
for path, key in [('lakefile.toml', 'lakefile_sha256'), ('lean-toolchain', 'lean_toolchain_sha256')]:
    assert path not in rows
    rows[path] = manifest[key]
paths = sorted(rows)
assert len(paths) == 1212
requests = ''.join(f'{EXPECTED_COMMIT}:{path}\n' for path in paths).encode()
result = subprocess.run(['git', '-C', str(ROOT), 'cat-file', '--batch'], input=requests,
                        capture_output=True, check=True)
assert not result.stderr
raw, pos = result.stdout, 0
for path in paths:
    end = raw.index(b'\n', pos)
    header = raw[pos:end].split()
    assert len(header) == 3 and header[1] == b'blob' and header[2].isdigit(), path
    pos = end + 1
    size = int(header[2])
    blob = raw[pos:pos + size]
    pos += size
    assert len(blob) == size and raw[pos:pos + 1] == b'\n', path
    pos += 1
    assert hashlib.sha256(blob).hexdigest() == rows[path], path
assert pos == len(raw)
print('PASS_PARENT_MANIFEST_GIT_BLOBS 1210 sources 2 configs', EXPECTED_MANIFEST, EXPECTED_COMMIT)
