#!/usr/bin/env python3
"""Resolve the selected project import closure of the fixed 80 iPRA client."""
from collections import deque
from hashlib import sha256
from pathlib import Path
import json, os, subprocess, sys, time

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
O = HERE / 'observations/attempt01'
BASE = D / 'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
RECEIPT = D / 'research/ten-positive-80-symbolic-ipra-client-prototype/observations/fixed-attempt01/terminal.json'
HELPER = D / 'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SYSROOT = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
EXPECTED_BASE = '09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed'
EXPECTED_HELPER = '886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f'
EXPECTED_ROOT = '3fb4bd73fad0ffe1d5a57a1fbff8d1d478460f686409dafa8422d0f90dee591a'

def need(ok, msg):
    if not ok:
        raise RuntimeError(msg)

def sha(p):
    return sha256(Path(p).read_bytes()).hexdigest()

def item(p):
    p = Path(p)
    return {'path': str(p), 'real_path': str(p.resolve(strict=True)), 'sha256': sha(p)}

def sample():
    rows = subprocess.run(['ps','-eo','pid=,comm=,rss=,args='], capture_output=True, text=True, check=True).stdout.splitlines()
    lean = [x.strip() for x in rows if len(x.split(None,3)) == 4 and x.split(None,3)[1] == 'lean']
    mem = int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])
    return {'time_ns': time.time_ns(), 'mem_available_kib': mem, 'lean': lean}

need(not O.exists(), 'observation exists')
need(sha(BASE) == EXPECTED_BASE and sha(HELPER) == EXPECTED_HELPER, 'base/helper drift')
base = json.loads(BASE.read_text())
need(base['status'] == 'PASS', 'base failed')
receipt = json.loads(RECEIPT.read_text())
need(receipt['exit'] == 0 and receipt['reason'] is None and receipt['pins'] == receipt['after'], 'fixed-client receipt invalid')
root = Path(receipt['output_root']) / 'Direct80SymbolicFixedIPRA.olean'
need(sha(root) == receipt['object_sha256'] == EXPECTED_ROOT, 'root object drift')
roots = [Path(receipt['output_root'])] + [Path(x) for x in receipt['lean_path'].split(':')]
project_roots = [r for r in roots if r != PACK and r != SYSROOT]
prior = base['post_headers']['project']
prior_outside = base['post_headers']['outside']
known = set(prior)
for path in project_roots:
    need(path.is_dir(), 'missing search root ' + str(path))
    known.update(str(x.relative_to(path))[:-6].replace('/', '.') for x in path.rglob('*.olean'))
known.add('Direct80SymbolicFixedIPRA')
pins = {str(p): sha(p) for p in (BASE, RECEIPT, HELPER, LEAN, HERE/'scan.py', root)}
pre = sample()
need(pre['mem_available_kib'] >= 8*1024**2 and len(pre['lean']) < 2, 'resource guard')
O.mkdir(parents=True)
todo = deque(['Direct80SymbolicFixedIPRA'])
seen, outside, fresh_headers, overlaps = {}, {}, {}, {}
batchno = 0
start = time.monotonic()
while todo:
    batch = []
    while todo and len(batch) < 64:
        name = todo.popleft()
        if name in seen or name in outside:
            continue
        rel = name.replace('.', '/') + '.olean'
        choices = [r / rel for r in roots + [SYSROOT] if (r / rel).is_file()]
        need(choices, 'unresolved import '+name)
        selected = item(choices[0])
        if name not in known:
            outside[name] = selected
            continue
        candidates = [item(p) for p in choices if any(p == r / rel for r in project_roots)]
        differences = [x for x in candidates if x['sha256'] != selected['sha256']]
        if differences:
            overlaps[name] = {'selected': selected, 'different_shadowed': differences}
        seen[name] = {'selected': selected, 'candidates': candidates}
        if name in prior:
            need(selected['sha256'] == prior[name]['record']['sha256'], 'selected differs from 90 base: '+name)
            todo.extend(prior[name]['imports'])
        else:
            batch.append((name, choices[0]))
    if not batch:
        continue
    guard = sample()
    need(guard['mem_available_kib'] >= 8*1024**2 and len(guard['lean']) < 2, 'resource guard while scanning')
    cmd = [str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER)] + [str(p) for _,p in batch]
    run = subprocess.run(cmd,capture_output=True,text=True,timeout=60)
    (O/f'header-{batchno:03}.stdout').write_text(run.stdout)
    (O/f'header-{batchno:03}.stderr').write_text(run.stderr)
    need(run.returncode == 0 and not run.stderr, 'header read failed')
    mapping = {str(p): n for n,p in batch}
    current = None
    headers = {}
    for line in run.stdout.splitlines():
        if line.startswith('BEGIN '):
            need(current is None and line[6:] in mapping, 'unexpected begin')
            current = mapping[line[6:]]
            need(current not in headers, 'duplicate begin')
            headers[current] = []
        elif line.startswith('IMPORT ') and current is not None:
            headers[current].append(line[7:])
        elif line == 'END' and current is not None:
            current = None
        else:
            raise RuntimeError('malformed header')
    need(current is None and set(headers) == set(mapping.values()), 'missing header')
    for name, imports in headers.items():
        fresh_headers[name] = imports
        todo.extend(imports)
    batchno += 1

for path, digest in pins.items():
    need(sha(path) == digest, 'input changed '+path)
for name, entry in list(seen.items()) + list(outside.items()):
    selected = entry['selected'] if name in seen else entry
    need(item(selected['path']) == selected, 'selected changed '+name)
post = sample()
result = {'status':'PASS', 'pins':pins, 'root':item(root), 'search_roots':[str(x) for x in roots],
          'project':seen, 'outside':outside, 'fresh_headers':fresh_headers, 'different_shadowed':overlaps,
          'prior_project_count':len(prior), 'prior_outside_count':len(prior_outside),
          'preflight':pre, 'postflight':post, 'header_batches':batchno, 'elapsed':time.monotonic()-start,
          'scope':'selected .olean closure; prior project headers reused after hash verification; package transitive, companions, dynamic and historical source-object ancestry not authenticated'}
(O/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','project':len(seen),'fresh_headers':len(fresh_headers),
                  'outside':len(outside),'different_shadowed':len(overlaps),'header_batches':batchno,
                  'elapsed':result['elapsed']}))
