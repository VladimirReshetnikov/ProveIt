#!/usr/bin/env python3
"""Validate the captured source and Foundation inputs; do not invoke Lean."""
import hashlib
import json
import os
import shutil
import sys
import time
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
SNAP = Path('/tmp/current14-standard-fresh-source-20261104')
SNAP_SHA = '1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749'
PROVIDER = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json')
PROVIDER_SHA = '7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OUT = HERE / 'preflight-observation.json'
if OUT.exists():
    raise SystemExit('refusing existing preflight observation')
def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1048576), b''):
            h.update(chunk)
    return h.hexdigest()
start = time.monotonic()
result = {'status': 'FAILED', 'scope': 'Point-in-time snapshot and declared provider guards, not a Lean build or a transitive/dynamic package audit.'}
try:
    if sha(SNAP / 'manifest.json') != SNAP_SHA or sha(PROVIDER) != PROVIDER_SHA:
        raise RuntimeError('snapshot or provider receipt hash mismatch')
    m = json.loads((SNAP / 'manifest.json').read_text())
    p = json.loads(PROVIDER.read_text())
    if m['target'] != 'DiophantineConsistency.IPRAStandardCurrentEndpointChecks' or len(m['order']) != 1000:
        raise RuntimeError('unexpected snapshot target or source count')
    if p['status'] != 'BUILT' or p['exit_code'] != 0:
        raise RuntimeError('Foundation receipt not BUILT/exit 0')
    root = Path(m['root'])
    for name in m['order']:
        row = m['sources'][name]
        if sha(SNAP / row['snapshot_path']) != row['sha256'] or sha(root / row['workspace_path']) != row['sha256']:
            raise RuntimeError('snapshot/source drift: ' + name)
    if sha(LEAN) != 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550':
        raise RuntimeError('Lean hash drift')
    foundation = Path(p['root']) / '.lake/build/lib/lean/Foundation'
    pkg = Path(p['overlay'])
    if (pkg / 'Foundation').resolve(strict=True) != foundation.resolve(strict=True):
        raise RuntimeError('Foundation overlay mismatch')
    for path, expected in p['declared_external_guard'].items():
        q = Path(path)
        if expected is None:
            if os.path.lexists(q):
                raise RuntimeError('unexpected companion or shadow: ' + path)
        elif not q.is_file() or str(q.resolve()) != expected['realpath'] or sha(q) != expected['sha256']:
            raise RuntimeError('external guard changed: ' + path)
    for rel, expected in p['foundation_artifacts'].items():
        q = foundation / rel
        if not q.is_file() or q.is_symlink() or sha(q) != expected:
            raise RuntimeError('Foundation artifact changed: ' + rel)
    found = {str(q.relative_to(foundation)) for q in foundation.rglob('*') if q.is_file() or q.is_symlink()}
    if found != set(p['foundation_artifacts']):
        raise RuntimeError('Foundation inventory mismatch')
    tops = {name.split('.')[0] for name in m['order']}
    tool = LEAN.resolve().parent.parent / 'lib/lean'
    for basedir in (pkg, tool):
        for top in tops:
            for ext in ('', '.olean', '.olean.private', '.olean.server', '.ir', '.ilean', '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash', '.so', '.dll', '.dylib'):
                if os.path.lexists(basedir / (top + ext)):
                    raise RuntimeError('project fallback shadow: ' + str(basedir / (top + ext)))
    free = shutil.disk_usage(SNAP).free
    if free < 4_000_000_000:
        raise RuntimeError('less than 4 GB free')
    result.update(status='PASS', snapshot_sha256=SNAP_SHA, provider_sha256=PROVIDER_SHA,
                  workspace_modules=len(m['order']), direct_external_modules=len(m['external_modules']),
                  external_guards=len(p['declared_external_guard']), foundation_artifacts=len(found),
                  project_namespace_count=len(tops), free_bytes=free, lean_sha256=sha(LEAN))
except Exception as exc:
    result['failure'] = repr(exc)
result['elapsed_seconds'] = round(time.monotonic()-start, 3)
result['script_sha256'] = sha(__file__)
with OUT.open('x') as f:
    json.dump(result, f, indent=2, sort_keys=True)
    f.write('\n')
print(json.dumps(result, sort_keys=True), flush=True)
if result['status'] != 'PASS':
    raise SystemExit(1)
