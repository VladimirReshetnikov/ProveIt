#!/usr/bin/env python3
"""Compare frozen declared source closures; this script never builds Lean."""
import hashlib
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise SystemExit('Optimized Python is unsupported')
here = Path(__file__).resolve().parent
repo = here.parents[3]
base_path = repo / 'Computability/DiophantineConsistency/research/current14-standard-fresh-rebuild-preflight/snapshot-manifest.json'
kernel_path = here / 'kernel-manifest.json'
masks_path = here / 'masks-manifest.json'
assembly = repo / 'Computability/DiophantineConsistency/research/current14-literal-port-assembly/Current14LiteralPorts.lean'
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def manifest(path, target):
    data = json.loads(path.read_text())
    if data['status'] != 'FROZEN_NOT_COMPILED' or data['target'] != target:
        raise ValueError(('unexpected manifest', str(path)))
    if len(data['sources']) != len(data['order']) or len(set(data['order'])) != len(data['order']):
        raise ValueError(('bad order', str(path)))
    return data
base = manifest(base_path, 'DiophantineConsistency.IPRAStandardCurrentEndpointChecks')
kern = manifest(kernel_path, 'DiophantineConsistency.CurrentKernel2011')
masks = manifest(masks_path, 'DiophantineConsistency.CurrentMaskRecipes2011')
all_rows = dict(kern['sources'])
for name, row in masks['sources'].items():
    if name in all_rows and all_rows[name]['sha256'] != row['sha256']:
        raise ValueError(('extension snapshots differ', name))
    all_rows[name] = row
shared = set(all_rows) & set(base['sources'])
for name in shared:
    if all_rows[name]['sha256'] != base['sources'][name]['sha256']:
        raise ValueError(('snapshot drift', name))
for name, row in all_rows.items():
    path = repo / row['workspace_path']
    if not path.is_file() or digest(path) != row['sha256']:
        raise ValueError(('current workspace drift', name))
additions = []
seen = set(base['sources'])
for data in (kern, masks):
    for name in data['order']:
        if name in seen:
            continue
        for dep in all_rows[name]['imports']:
            if dep in all_rows and dep not in seen:
                raise ValueError(('invalid extension order', name, dep))
        additions.append(name)
        seen.add(name)
extra_external = sorted((set(kern['external_modules']) | set(masks['external_modules'])) - set(base['external_modules']))
result = {
    'status': 'SOURCE_PLAN_ONLY',
    'base_manifest_sha256': digest(base_path),
    'kernel_manifest_sha256': digest(kernel_path),
    'masks_manifest_sha256': digest(masks_path),
    'assembly_source_sha256': digest(assembly),
    'base_project_count': len(base['sources']),
    'extension_union_count': len(all_rows),
    'shared_with_base_count': len(shared),
    'extra_project_count': len(additions),
    'extra_project_build_order': additions,
    'new_declared_external_modules': extra_external,
    'scope': 'Point-in-time source-declared graph comparison; not a Lean build, provider authentication, or a complete dependency discovery.',
}
print(json.dumps(result, indent=2, sort_keys=True))
