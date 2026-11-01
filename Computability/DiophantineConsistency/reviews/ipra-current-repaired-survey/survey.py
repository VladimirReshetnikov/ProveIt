#!/usr/bin/env python3
"""Freeze a conservative current-source survey; this is not a build or proof."""
import collections
import graphlib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REVIEWS = ROOT / 'Computability/DiophantineConsistency/reviews'
OLD = REVIEWS / 'ipra-adaptive-native-current-rebase/manifest.json'
PLAN = REVIEWS / 'ipra-frozen-repair-plan-v2/manifest.json'
PARENT = Path('/tmp/ipra-frozen-ancestry-repair-6ftdeyrq')
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
TOOL = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
EXT = {'Foundation', 'Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Qq',
       'Aesop', 'Plausible', 'ProofWidgets', 'ImportGraph', 'LeanSearchClient', 'Lake'}
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.olean.hash',
            '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean', '.ilean.hash')
TARGET = 'DiophantineConsistency.IPRAAdaptiveNativeZFCChecks'
sha = lambda b: hashlib.sha256(b).hexdigest()
def filehash(p):
    return sha(Path(p).read_bytes())
def load(p):
    return json.loads(Path(p).read_text())

old, plan, state = load(OLD), load(PLAN), load(PARENT / 'state.json')
assert state['status'] == 'PASS' and state['manifest_sha256'] == filehash(PLAN)
assert [r['name'] for r in state['records']] == plan['order']
assert all(r['exit'] == 0 and not r['warnings'] for r in state['records'])
observed_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
roots = {}
for name, path in old['source_files'].items():
    suffix = name.replace('.', '/') + '.lean'
    assert path.endswith(suffix), (name, path)
    root = path[:-len(suffix)]
    namespace = name.split('.')[0]
    assert namespace not in roots or roots[namespace] == root
    roots[namespace] = root

sources, graph, external = {}, {}, set()
def source(name):
    ns = name.split('.')[0]
    if ns not in roots:
        raise ValueError(('unknown project namespace', name))
    path = ROOT / roots[ns] / (name.replace('.', '/') + '.lean')
    if not path.is_file():
        raise ValueError(('missing project source', name, str(path)))
    return path
def visit(name):
    if name in sources:
        return
    path = source(name)
    raw = path.read_bytes()
    text = raw.decode('utf-8')
    # Read only the header, including nested block and line comments. Stop at
    # the first non-header command so prose and strings in the body cannot be
    # mistaken for imports. Reject unsupported header syntax.
    imports = []
    depth = 0
    for line in text.splitlines():
        clean = ''
        pos = 0
        while pos < len(line):
            pair = line[pos:pos+2]
            if depth:
                if pair == '/-':
                    depth += 1
                    pos += 2
                elif pair == '-/':
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            elif pair == '/-':
                depth = 1
                pos += 2
            elif pair == '--':
                break
            else:
                clean += line[pos]
                pos += 1
        clean = clean.strip()
        if not clean:
            continue
        match = re.fullmatch(r'import\s+([A-Za-z_][\w.]*)', clean)
        if match:
            imports.append(match.group(1))
        elif clean.startswith('import ') or clean.startswith('public import '):
            raise ValueError(('unsupported import syntax', name, line))
        elif clean in ('prelude', 'module'):
            continue
        else:
            break
    sources[name] = {'path': str(path.relative_to(ROOT)), 'sha256': sha(raw),
                     'imports': imports}
    graph[name] = [i for i in imports if i.split('.')[0] not in EXT]
    external.update(i for i in imports if i.split('.')[0] in EXT)
    for dependency in graph[name]:
        visit(dependency)
visit(TARGET)

records = {r['name']: r for r in state['records']}
inventory = plan['parent_inventory']
selected = {}
for name in sources:
    rel = name.replace('.', '/') + '.olean'
    path = PARENT / 'lib' / rel
    if not path.is_file():
        continue
    digest = filehash(path)
    if name in records:
        assert digest == records[name]['object_sha256'], name
    elif rel in inventory:
        assert digest == inventory[rel]['sha256'], name
    else:
        raise ValueError(('unrecorded selected project object', name))
    selected[name] = {'path': str(path.resolve()), 'sha256': digest}

nodes = {(v['module'], v['sha256'], v['physical_path']): v
         for v in plan['origin_nodes'].values()}
reverse = collections.defaultdict(set)
for name, deps in graph.items():
    for dep in deps:
        reverse[dep].add(name)
reasons = collections.defaultdict(list)
all_old = plan['source_sha256']
# Include changes to modules used in original object environments even if a
# later source edit removed them from the current import graph.
for name, previous in all_old.items():
    try:
        path = source(name)
    except ValueError:
        reasons[name].append('previous source unavailable')
        continue
    if filehash(path) != previous:
        reasons[name].append('source differs from frozen parent')
for name in sources:
    if name not in all_old:
        reasons[name].append('new source')
    if name not in selected:
        reasons[name].append('no selected parent object')
        continue
    if name in records:
        dependencies = records[name]['direct_imports']
        env = {dep: v['sha256'] for dep, v in dependencies.items()
               if dep.split('.')[0] not in EXT}
        for dep, v in dependencies.items():
            if dep.split('.')[0] in EXT and filehash(v['resolved_path']) != v['sha256']:
                reasons[name].append('repaired direct external changed: ' + dep)
    else:
        key = (name, selected[name]['sha256'], selected[name]['path'])
        node = nodes.get(key)
        if node is None:
            reasons[name].append('untraced original physical provider')
            continue
        env = node['project_environment']
    for dep, digest in env.items():
        reverse[dep].add(name)
        rel = dep.replace('.', '/') + '.olean'
        path = PARENT / 'lib' / rel
        if not path.is_file() or filehash(path) != digest:
            reasons[name].append('original project environment differs: ' + dep)

dirty = set(reasons)
queue = list(dirty)
while queue:
    dep = queue.pop()
    for owner in reverse[dep]:
        if owner not in dirty:
            dirty.add(owner)
            reasons[owner].append('depends on changed or unverified ' + dep)
            queue.append(owner)
affected = dirty & sources.keys()
order = list(graphlib.TopologicalSorter({n: [d for d in graph[n] if d in affected]
                                         for n in affected}).static_order())
assert TARGET in affected

external_files = {}
for name in sorted(external):
    stem = name.replace('.', '/')
    selected_external = next((root / (stem + '.olean') for root in (PKG, TOOL)
                              if (root / (stem + '.olean')).is_file()), None)
    if selected_external is None:
        raise ValueError(('missing external object', name))
    companions = {}
    for root in (PKG, TOOL):
        for suffix in SUFFIXES:
            path = root / (stem + suffix)
            if path.is_file():
                companions[str(path)] = {'sha256': filehash(path), 'realpath': str(path.resolve())}
            else:
                assert not os.path.lexists(path), ('broken symlink', str(path))
                companions[str(path)] = None
    external_files[name] = {'selected': str(selected_external.resolve()), 'companions': companions}

out = HERE / 'sources'
assert not out.exists(), 'refusing to overwrite frozen snapshot'
for name, info in sources.items():
    dest = out / (name.replace('.', '/') + '.lean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / info['path'], dest)
    assert filehash(dest) == info['sha256']
# Detect workspace drift across the complete graph at snapshot time.
drift = {name: {'frozen': v['sha256'], 'current': filehash(ROOT / v['path'])}
         for name, v in sources.items() if filehash(ROOT / v['path']) != v['sha256']}
result = {'target': TARGET, 'observed_head': observed_head, 'parent': str(PARENT),
          'parent_state_sha256': filehash(PARENT / 'state.json'),
          'repair_plan_sha256': filehash(PLAN), 'old_manifest_sha256': filehash(OLD),
          'surveyor_sha256': filehash(__file__), 'roots': roots, 'sources': sources,
          'selected_project_objects': selected, 'dirty_reasons': dict(reasons),
          'order': order, 'external': external_files, 'workspace_drift': drift,
          'boundary': 'Survey only: inherited external transitive and dynamic ancestry, '
                      'and all 848-ancestor limitations remain; no Lean build has run.'}
(HERE / 'manifest.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
print(json.dumps({'sources': len(sources), 'affected': len(order), 'external_modules': len(external),
                  'drift': len(drift), 'dirty_reasons': len(reasons)}, sort_keys=True))
