"""Capture current committed inputs; this never launches the native checker."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse, json
from common import *
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--root', type=Path, required=True); p.add_argument('--source-commit', required=True)
p.add_argument('--plan', type=Path, required=True); p.add_argument('--output', type=Path, required=True)
a = p.parse_args(); root = a.root.resolve(); plan = json.loads(a.plan.read_text())
require(list(plan) == ['core', 'shared', 'supplemental'], 'Expected core/shared/supplemental order')
graph = graph_for(root, [r for spec in plan.values() for r in spec['roots']])
modes = describe_modes(root, plan, graph)
for label, spec in plan.items():
    for key in ('module_count', 'input_count', 'source_lines'):
        require(modes[label][key] == spec[key], 'Unexpected measured ' + label + '/' + key)
paths = {module_path(m) for m in graph} | set(CONFIGS + FACADES + [INVENTORY])
base = Path(__file__).resolve().parent
snap = {'schema_version': 1, 'captured_at': now(), 'root': str(root), 'source_commit': a.source_commit,
        'modes': modes, 'graph': graph, 'source_hashes': {p: sha(root / p) for p in sorted(paths)},
        'tools': {str(base / p): sha(base / p) for p in ('common.py', 'capture.py', 'run.py')},
        'plan': {'path': str(a.plan.resolve()), 'sha256': sha(a.plan)}}
source_guard(snap); write_new(a.output, snap)
print(json.dumps({'snapshot': str(a.output), 'sha256': sha(a.output), 'source_commit': a.source_commit,
                  'counts': {k: v['module_count'] for k, v in modes.items()},
                  'combined_modules': len(graph), 'protected_files': len(paths)}, indent=2))
