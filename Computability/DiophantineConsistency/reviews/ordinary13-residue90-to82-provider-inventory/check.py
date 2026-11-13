#!/usr/bin/env python3
"""Check a bounded, read-only snapshot of the 90-to-82 source/provider cut."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
DATA = json.loads((HERE / 'inventory.json').read_text())

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def imports(path):
    result = []
    for line in path.read_text().splitlines():
        match = re.fullmatch(r'\s*import\s+(.+?)\s*', line)
        if match:
            result.extend(match.group(1).split())
    return result

def observation(path):
    return {'exists': path.is_file(), 'sha256': digest(path) if path.is_file() else None}

nodes = DATA['research_modules']
for name, info in nodes.items():
    path = ROOT / info['source']
    assert digest(path) == info['sha256'], (name, 'source digest')
    assert imports(path) == info['imports'], (name, 'imports')
    assert observation(ROOT / info['workspace_object']) == info['workspace_object_observed'], (name, 'object')

for name, info in DATA['direct_frontier'].items():
    assert observation(ROOT / info['source']) == info['source_observed'], (name, 'source')
    assert observation(ROOT / info['object']) == info['object_observed'], (name, 'object')

assert digest(ROOT / 'lean-toolchain') == DATA['lean_toolchain_sha256']
seen, active, order, frontier = set(), set(), [], set()
def visit(name):
    assert name not in active, ('cycle', name)
    if name in seen:
        return
    active.add(name)
    for dep in nodes[name]['imports']:
        if dep in nodes:
            visit(dep)
        else:
            frontier.add(dep)
    active.remove(name)
    seen.add(name)
    order.append(name)
visit(DATA['root_module'])
assert seen == set(nodes)
assert frontier == set(DATA['direct_frontier'])
assert order == DATA['topological_order']
print('Verified pinned source hashes, literal imports, topological closure, and bounded source/object observations:')
print(f"{len(nodes)} research modules; {len(frontier)} direct qualified providers; root {DATA['root_module']}.")
print('No Lean execution, transitive provider authentication, or endpoint proof is asserted.')
