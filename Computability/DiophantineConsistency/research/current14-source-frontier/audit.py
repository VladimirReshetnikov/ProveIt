#!/usr/bin/env python3
"""Compare a pinned historical endpoint import graph with workspace sources.

This is a source-directed planning audit, not a Lean replay.  Output is JSON;
no repository files or build artifacts are modified.
"""
import hashlib
import json
import re
import subprocess
from pathlib import Path

if not __debug__:
    raise RuntimeError('assertions required; do not use Python -O')

HERE = Path(__file__).resolve().parent
ROOT = Path(subprocess.check_output(['git', '-C', str(HERE), 'rev-parse', '--show-toplevel'], text=True).strip())
MANIFEST = HERE / 'historical-manifest.json'
PREPARATION = ROOT / 'Computability/DiophantineConsistency/reviews/ipra-standard-current14-historical-pair-terminal/preparation.json'
EXPECTED_MANIFEST = 'ad373be2f3dbecd4beae4e44141c163f86294641e18bd9e4eacf000396fe0581'
EXPECTED_PREPARATION = '53cedecdd1e357cbb800a51a783fa4cf7c0c01591e493080e7c7576bb2767d9d'
TARGET = 'DiophantineConsistency.IPRAStandardCurrentEndpointChecks'

def sha(data):
    return hashlib.sha256(data).hexdigest()

manifest_bytes = MANIFEST.read_bytes()
preparation_bytes = PREPARATION.read_bytes()
assert sha(manifest_bytes) == EXPECTED_MANIFEST
assert sha(preparation_bytes) == EXPECTED_PREPARATION
manifest = json.loads(manifest_bytes)
preparation = json.loads(preparation_bytes)
assert preparation['new_snapshot_sha256'] == EXPECTED_MANIFEST
assert manifest['target'] == TARGET
sources = manifest['sources']
assert len(sources) == manifest['project_modules'] == 1226

# The manifest explicitly lists direct source imports; external modules remain
# outside this project graph.  The source plan is not a Lean dynamic-load trace.
ancestors, stack = set(), [TARGET]
while stack:
    m = stack.pop()
    if m in ancestors or m not in sources:
        continue
    ancestors.add(m)
    stack.extend(sources[m]['imports'])
assert len(ancestors) == 1000

changed = []
missing = []
import_drifts = []
for m in sorted(ancestors):
    record = sources[m]
    path = ROOT / record['workspace_path']
    if not path.is_file():
        missing.append({'module': m, 'path': record['workspace_path']})
        continue
    data = path.read_bytes()
    current = sha(data)
    if current != record['sha256']:
        # Check the changed source's explicit import declarations.  This is
        # a simple line scan, not a Lean parser: uncommon syntax or text inside
        # block comments can be missed or misidentified.
        text = data.decode('utf-8')
        imports = []
        for line in re.findall(r'^import[ \t]+([^\n]*)', text, re.MULTILINE):
            imports.extend(line.split('--', 1)[0].split())
        changed.append({'module': m, 'path': record['workspace_path'],
                        'historical_sha256': record['sha256'], 'current_sha256': current})
        if imports != record['imports']:
            import_drifts.append({'module': m, 'historical': record['imports'], 'current': imports})

# Missing or import-changed files make the old-graph closure incomplete.
affected = {entry['module'] for entry in changed + missing}
while True:
    next_nodes = {m for m in ancestors if any(dep in affected for dep in sources[m]['imports'])}
    if next_nodes <= affected:
        break
    affected |= next_nodes

result = {
    'status': 'SOURCE_FRONTIER_ONLY',
    'workspace_head': subprocess.check_output(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True).strip(),
    'target': TARGET,
    'historical_manifest_sha256': sha(manifest_bytes),
    'preparation_sha256': sha(preparation_bytes),
    'declared_project_ancestors': len(ancestors),
    'changed': changed,
    'missing': missing,
    'import_drifts': import_drifts,
    'affected_on_historical_graph_count': len(affected),
    'affected_on_historical_graph': sorted(affected),
    'target_affected': TARGET in affected,
    'scope': 'Historical manifest direct-source import graph only; no Lean build, object authentication, external packages or dynamic loads.'
}
print(json.dumps(result, indent=2, sort_keys=True))
