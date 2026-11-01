#!/usr/bin/env python3
"""Observe Lake namespace routing during/after the Foundation build.

This is a point-in-time observation; it is not a continuous trace of which
files Lean loaded or an authentication of package-transitive dependencies.
"""
import hashlib
import json
import os
from pathlib import Path
import sys
import build_all as build

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

if len(sys.argv) != 3:
    raise SystemExit('usage: observe_namespaces.py /absolute/build/root /new/output.json')
root = Path(sys.argv[1]).resolve(strict=True)
out = Path(sys.argv[2])
if sha(build.MANIFEST) != build.MANIFEST_SHA256:
    raise RuntimeError('manifest identity mismatch')
manifest = json.loads(build.MANIFEST.read_text())
build.check_inputs(root, manifest)
env = dict(os.environ, LEAN_NUM_THREADS='1')
for variable in build.SANITIZED:
    env.pop(variable, None)
sources, external, guard, path_text = build.direct_external_inputs(
    root, manifest['historical_module_names'], env)
build.check_guard(guard)
roots = [Path(p) for p in path_text.split(':')]
inventory = {}
for namespace in sorted({name.split('.')[0] for name in external} | {'Foundation'}):
    rows = []
    for base in roots:
        directory, top_obj = base / namespace, base / (namespace + '.olean')
        if directory.is_dir() or top_obj.is_file():
            rows.append({'root': str(base), 'root_realpath': str(base.resolve()),
                         'directory_realpath': str(directory.resolve()) if directory.is_dir() else None,
                         'top_object_sha256': sha(top_obj) if top_obj.is_file() else None})
    if len(rows) != 1:
        raise RuntimeError(f'namespace has {len(rows)} providers: {namespace}')
    inventory[namespace] = rows
result = {'root': str(root), 'manifest_sha256': sha(build.MANIFEST),
          'builder_sha256': sha(Path(build.__file__)),
          'observer_sha256': sha(Path(__file__)), 'lake_lean_path': path_text,
          'foundation_source_count': len(sources), 'external_modules': external,
          'guard_count': len(guard), 'guard': guard, 'namespaces': inventory,
          'scope': 'Point-in-time source-declared namespace survey; no continuous or dynamic-import trace.'}
with out.open('x') as f:
    json.dump(result, f, indent=2, sort_keys=True)
    f.write('\n')
print('PASS:', len(inventory), 'unique namespaces;', len(guard), 'guard paths')
