#!/usr/bin/env python3
"""Independent static audit of the AQ22 author plan; does not run Lean."""
import copy
import hashlib
import json
import pathlib
import re
import subprocess
import sys

if not __debug__:
    raise SystemExit('optimized Python is not permitted')
ROOT = pathlib.Path(__file__).resolve().parents[4]
BASE = ROOT / 'Computability/DiophantineConsistency'
PLAN = BASE / 'research/adaptive-aq22-proof/author-additions.json'
PRIOR = BASE / 'research/ipra-standard-aq26/author-additions.json'
PARENT = pathlib.Path('/tmp/ipra-aq29-fresh-source-closure-v2/manifest.json')
PIN = 'bd19027b6835198b97bd58b5d8cb58c1849fcd99'
PLAN_SHA = '3c5df040f94803b19ccbed14ec93be2e3de2e16ed9c31efd9bcfb531373200df'
PRIOR_SHA = '1a04dbd22330a61cb2f134f6875513e9457190fca0da7127f500fe6098db1f8b'
PARENT_SHA = '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
NEW = ['AdaptiveAQ22Literal', 'AdaptiveAQ22Zeros', 'AdaptiveAQ22Maps',
       'AdaptiveAQ22Transport', 'AdaptiveAQ22', 'IPRAAQ22Native', 'IPRAStandardAQ22']

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def digest(b):
    return hashlib.sha256(b).hexdigest()

def read_json(p, expected):
    b = p.read_bytes()
    require(digest(b) == expected, f'hash mismatch: {p}')
    return json.loads(b)

plan = read_json(PLAN, PLAN_SHA)
prior = read_json(PRIOR, PRIOR_SHA)
parent = read_json(PARENT, PARENT_SHA)
parent_names = set(parent['order'])
parent_external = set(parent['external_modules'])
require(len(parent_names) == len(parent['order']) == 1210, 'parent coverage')
# Cache independent Git blob/mode lookup, and check worktree matches them.
blobs = {}
for name, row in plan['sources'].items():
    path = row['workspace_path']
    out = subprocess.check_output(['git', 'ls-tree', '-z', PIN, '--', path], cwd=ROOT)
    require(out.startswith(b'100644 blob ') and out.endswith(b'\t'+path.encode()+b'\0'), f'tracked mode/path: {name}')
    blob = subprocess.check_output(['git', 'show', f'{PIN}:{path}'], cwd=ROOT)
    require((ROOT / path).read_bytes() == blob, f'worktree differs: {name}')
    blobs[name] = blob

def check(m):
    order = m['order']; rows = m['sources']; reports = m['axiom_reports']
    require(m['source_commit'] == PIN and m['parent_manifest_sha256'] == PARENT_SHA, 'pins')
    require(m['status'] == 'FROZEN_ADDITIONS', 'status')
    require(len(order) == 37 and len(set(order)) == 37 and set(order) == set(rows), 'module coverage')
    require(order[:30] == prior['order'] and order[30:] == ['DiophantineConsistency.'+s for s in NEW], 'order/baseline')
    require(all(rows[n] == prior['sources'][n] and reports.get(n) == prior['axiom_reports'].get(n) for n in order[:30]), 'prior source/policy mismatch')
    require(not parent_names.intersection(order), 'shadowed parent module')
    require(len({v['workspace_path'] for v in rows.values()}) == len(order), 'duplicate source')
    require(set(reports) <= set(order), 'report outside plan')
    built = set(parent_names)
    count = 0
    for name in order:
        b = blobs[name]; row = rows[name]; s = b.decode()
        require(digest(b) == row['sha256'], f'source hash: {name}')
        imports = re.findall(r'^import\s+([\w.\']+)\s*$', s, re.M)
        require(len(set(imports)) == len(imports) and set(imports) == set(row['imports']), f'import list: {name}')
        for dep in imports:
            require(dep in built or dep in parent_external, f'unknown/not-yet-built import {name}: {dep}')
        actual = re.findall(r'^\s*#print\s+axioms\s+([\w.\']+)\s*$', s, re.M)
        wanted = reports.get(name, [])
        require(len(actual) == len(wanted) and all(w == a or w.endswith('.'+a) for a,w in zip(actual,wanted)), f'diagnostic declarations: {name}')
        count += len(actual)
        built.add(name)
    require(count == 94, 'report count')
    return count

count = check(plan)
# Mutation checks show that omitted checks, misordered prerequisites, and changed identities fail.
mutations = {}
for label, edit in [
    ('missing endpoint diagnostic', lambda m: m['axiom_reports'][m['order'][-1]].pop()),
    ('out-of-order dependency', lambda m: m['order'].__setitem__(slice(-7, -5), list(reversed(m['order'][-7:-5])))),
    ('altered source identity', lambda m: m['sources'][m['order'][-1]].__setitem__('sha256', '0'*64)),
    ('missing source row', lambda m: m['sources'].pop(m['order'][-1])),
]:
    bad = copy.deepcopy(plan)
    edit(bad)
    try:
        check(bad)
    except (ValueError, KeyError) as e:
        mutations[label] = str(e)
    else:
        raise SystemExit('mutation was accepted: ' + label)
print(json.dumps({'status':'PASS', 'scope':'static manifest/source audit only, no Lean replay',
    'plan_sha256': PLAN_SHA, 'source_commit': PIN, 'parent_manifest_sha256': PARENT_SHA,
    'parent_modules':len(parent_names), 'additions':len(plan['order']), 'prior_additions':30,
    'aq22_additions':7, 'diagnostic_declarations':count, 'mutation_rejections':mutations}, indent=2, sort_keys=True))
