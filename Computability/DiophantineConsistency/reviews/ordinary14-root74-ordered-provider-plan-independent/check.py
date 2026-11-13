#!/usr/bin/env python3
"""Independently compare the recorded candidate order to current source headers.

This deliberately does not resolve Lean imports, inspect object ancestry, or
invoke Lean. Its input is a pinned point-in-time observation.
"""
from pathlib import Path
import hashlib
import json

D = Path(__file__).resolve().parents[2]
plan_path = D / 'research/ordinary14-root74-ordered-provider-plan/plan.json'
raw = plan_path.read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'ac8e0e6c3ca24a5356d4197fe2aaa9bdfe81b7b56a9d554ffa4a9d37d527ffe8'
plan = json.loads(raw)
stages = plan['candidate_stages']
front = plan['qualified_frontier_objects']
external = plan['external_cut_objects']
assert len(stages) == 162 and len(front) == 31 and len(external) == 4
assert all(s['kind'] == 'qualified-source-candidate' for s in stages[:3])
assert all(s['kind'] == 'bare-inert-overlay' for s in stages[3:])
assert stages[-1]['module'] == 'Root74Endpoint'
modules = {s['module']: s for s in stages}
assert len(modules) == len(stages)
assert set(front).isdisjoint(external) and set(modules).isdisjoint(front.keys() | external.keys())

# All 162 inspected sources begin with ordinary, single-line import commands.
# Fail if their header shape changes; this is not a general Lean parser.
def header(source):
    imports = []
    for line in source.splitlines():
        t = line.strip()
        if not t:
            continue
        if not t.startswith('import '):
            break
        tokens = t.split()
        assert len(tokens) == 2 and tokens[0] == 'import', t
        assert all(part.isidentifier() for part in tokens[1].split('.')), t
        imports.append(tokens[1])
    assert imports
    return imports

ready = set(front) | set(external)
edge_count = 0
for stage in stages:
    path = D / stage['source']
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == stage['sha256'], stage['module']
    parsed = header(data.decode('utf-8'))
    claimed = stage['lexical_imports']
    assert len(parsed) == len(claimed) and sorted(parsed) == sorted(claimed), stage['module']
    assert set(parsed) <= ready, (stage['module'], sorted(set(parsed)-ready))
    edge_count += len(parsed)
    ready.add(stage['module'])

# Confirm every proposed stage is in the lexical endpoint ancestry, not just
# included in an arbitrary topological ordering.
seen, todo = set(), ['Root74Endpoint']
while todo:
    current = todo.pop()
    if current not in seen:
        seen.add(current)
        todo.extend(i for i in modules[current]['lexical_imports'] if i in modules)
assert seen == set(modules)

def digest_file(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

# Read actual current objects independently of the original checker. Their
# byte matches are observations, not producer or transitive-closure proofs.
roots = {'p72': 0, 'base': 0}
for module, record in {**front, **external}.items():
    path = Path(record['path'])
    assert path.is_file() and str(path.resolve(strict=True)) == record['realpath'], module
    assert digest_file(path) == record['sha256'], module
    if module in front:
        real = record['realpath']
        if real.startswith('/tmp/p72-current-base-extension-attempt02-20261105/lib/'):
            roots['p72'] += 1
        elif real.startswith('/tmp/current14-standard-fresh-build-20261104/lib/'):
            roots['base'] += 1
        else:
            raise AssertionError((module,real))
assert roots == {'p72':24, 'base':7}
print(json.dumps({'scope':'bounded independent header, byte, lexical order and observed-object checks; no Lean resolver or provider-closure claim',
                  'candidate_stages':len(stages), 'actual_header_import_edges':edge_count,
                  'endpoint_reachable_stages':len(seen), 'frontier_objects':len(front),
                  'external_objects':len(external), 'frontier_resolved_roots':roots,
                  'pinned_plan_sha256':hashlib.sha256(raw).hexdigest()}, sort_keys=True, indent=2))
