#!/usr/bin/env python3
"""Recheck saved paths, import traversal, overlap and prior companion hashes."""
from collections import deque
from hashlib import sha256
from pathlib import Path
import json

H = Path(__file__).resolve().parent
D = H.parents[1]
SCAN = H/'observations/attempt01/result.json'
BASE = D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'

def sha(p):
    return sha256(Path(p).read_bytes()).hexdigest()

def need(ok, msg):
    if not ok:
        raise RuntimeError(msg)

x = json.loads(SCAN.read_text())
b = json.loads(BASE.read_text())
need(x['status'] == 'PASS', 'scan failed')
for p, digest in x['pins'].items():
    need(sha(p) == digest, 'input drift '+p)
prior = b['post_headers']['project']
roots = [Path(p) for p in x['search_roots']]
pack = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
sysroot = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
graph = {name: data['imports'] for name, data in prior.items()}
graph.update(x['fresh_headers'])
todo, seen, outside = deque(['Direct80SymbolicFixedIPRA']), set(), set()
while todo:
    name = todo.popleft()
    if name in seen or name in outside:
        continue
    if name not in graph:
        outside.add(name)
        continue
    seen.add(name)
    todo.extend(graph[name])
need(seen == set(x['project']) and outside == set(x['outside']), 'closure mismatch')
companion_count = 0
for name, ent in x['project'].items():
    choices = ent['candidates']
    need(choices and choices[0] == ent['selected'], 'first selection mismatch '+name)
    rel = name.replace('.', '/')+'.olean'
    actual = [str(r/rel) for r in roots+[sysroot] if (r/rel).is_file()]
    project_actual = [str(r/rel) for r in roots if r != pack and (r/rel).is_file()]
    need(actual and actual[0] == ent['selected']['path'], 'resolution changed '+name)
    need(project_actual == [c['path'] for c in choices], 'candidate list changed '+name)
    for c in choices:
        p = Path(c['path'])
        need(str(p.resolve(strict=True)) == c['real_path'] and sha(p) == c['sha256'], 'candidate drift '+name)
        need(c['sha256'] == ent['selected']['sha256'], 'differing project overlap '+name)
    if name in prior:
        q = ent['selected']['path'][:-6]
        for ext, old in prior[name]['companions'].items():
            f = Path(q+ext)
            need(f.is_file() == (old is not None), 'companion presence '+name+ext)
            if old is not None:
                need(sha(f) == old['sha256'], 'companion digest '+name+ext)
                companion_count += 1
for name, ent in x['outside'].items():
    p = Path(ent['path'])
    rel = name.replace('.', '/')+'.olean'
    actual = [str(r/rel) for r in roots+[sysroot] if (r/rel).is_file()]
    need(actual and actual[0] == ent['path'], 'outside resolution changed '+name)
    need(str(p.resolve(strict=True)) == ent['real_path'] and sha(p) == ent['sha256'], 'outside drift '+name)
need(not x['different_shadowed'], 'shadowed conflicts')
print(json.dumps({'status':'PASS', 'project':len(seen), 'outside':len(outside),
                  'fresh_headers':len(x['fresh_headers']), 'prior_companions':companion_count,
                  'different_shadowed':0, 'scan_sha256':sha(SCAN)},sort_keys=True))
