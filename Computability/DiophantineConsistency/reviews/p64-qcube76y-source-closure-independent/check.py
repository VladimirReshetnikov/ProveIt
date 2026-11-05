#!/usr/bin/env python3
"""Read-only recomputation from the stored 76Y source plan; no Lean or build."""
import hashlib,json,os,subprocess,sys
from collections import Counter
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent; root=here.parents[3]
research=root/'Computability/DiophantineConsistency/research'
plan=research/'p64-qcube76y-source-closure-plan/result.json'
basepath=research/'current14-standard-fresh-rebuild-preflight/snapshot-manifest.json'
providerpath=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
if sha(plan)!='bc594561278d7242d5f377b333b5ef6c1af8db817d05e3b79c70bd80565bd5bd' or sha(basepath)!='1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749':raise RuntimeError('plan or base pin drift')
x=json.loads(plan.read_text());base=json.loads(basepath.read_text());src=x['sources']; issues=[]
project={n for n,r in src.items() if r['kind']=='project'}; local={n for n,r in src.items() if r['kind']=='local'}
if len(project)!=1608 or len(local)!=42 or project&local or len(src)!=1650:issues.append('source counts')
reachable=set();todo=[x['target']];external=set()
while todo:
    name=todo.pop()
    if name in reachable or name in external:continue
    if name not in src:external.add(name);continue
    reachable.add(name);todo.extend(src[name]['imports'])
if reachable!=set(src) or len(external)!=80:issues.append('stored graph reachability/external count')
if sorted(n for n in external if '.' not in n)!=['Init']:issues.append('unexpected unresolved dotless import')
prefixes=Counter(n.split('.')[0] for n in external)
if dict(prefixes)!={'Foundation':37,'Mathlib':41,'Lean':1,'Init':1}:issues.append('unexpected external namespace')
shared=project&set(base['sources']);new=project-set(base['sources'])
changed={n for n in shared if src[n]['sha256']!=base['sources'][n]['sha256'] or src[n]['imports']!=base['sources'][n]['imports']}
if len(shared)!=919 or len(new)!=689 or changed:issues.append('base overlap mismatch')
dirty=set(new)|changed
while True:
    newer=dirty|{n for n in project if any(d in dirty for d in src[n]['imports'])}
    if newer==dirty:break
    dirty=newer
if len(dirty)!=689 or dirty&shared:issues.append('reverse dirty closure mismatch')
def verify_order(order,nodes,base_nodes):
    if len(order)!=len(nodes) or set(order)!=nodes:return False
    seen=set(base_nodes)
    for n in order:
        if any(d in nodes|base_nodes and d not in seen for d in src[n]['imports']):return False
        seen.add(n)
    return True
if not verify_order(x['project_rebuild_order'],dirty,shared):issues.append('project rebuild order')
if not verify_order(x['local_order'],local,project):issues.append('flat module order')
if any(d in local for n in project for d in src[n]['imports']):issues.append('project-to-flat edge')
paths=[src[n]['path'] for n in src]
for n,row in src.items():
    p=root/row['path']
    if not p.is_file() or sha(p)!=row['sha256']:issues.append('workspace source hash: '+n)
tracked={b.decode() for b in subprocess.check_output(['git','ls-files','-z','--',*paths],cwd=root).split(b'\0') if b}
diff={b.decode() for b in subprocess.check_output(['git','diff','--name-only','-z','HEAD','--',*paths],cwd=root).split(b'\0') if b}
if set(paths)!=tracked or diff:issues.append('tracked/HEAD source mismatch')
provider=json.loads(providerpath.read_text()); overlay=Path(provider['overlay']); sysroot=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
missing=[]
for name in sorted(external):
    rel=name.replace('.','/')+'.olean'
    if not any((r/rel).is_file() for r in (overlay,sysroot)):missing.append(name)
if missing:issues.append('unavailable external objects: '+','.join(missing))
newextern=sorted(external-set(base['external_modules'])-{'Init'})
if newextern!=x['new_direct_external_modules'] or len(newextern)!=3:issues.append('new external set')
newpaths={}
for n in newextern:
    rel=n.replace('.','/')+'.olean'; p=overlay/rel
    matches=[k for k in provider['declared_external_guard'] if k.endswith('/'+rel)]
    if not p.is_file() or matches:issues.append('new external observation mismatch: '+n)
    newpaths[n]={'sha256':sha(p),'realpath':str(p.resolve()),'matching_guard_paths':len(matches)}
result={'status':'PASS_STORED_GRAPH_AND_CURRENT_BYTES' if not issues else 'ISSUES','script_sha256':sha(__file__),
        'plan_sha256':sha(plan),'base_sha256':sha(basepath),'provider_receipt_sha256':sha(providerpath),
        'local':len(local),'project':len(project),'base_shared':len(shared),'project_additional':len(new),
        'external':len(external),'external_prefix_counts':dict(sorted(prefixes.items())),
        'dotless_external':sorted(n for n in external if '.' not in n),'external_objects_missing':missing,
        'new_external_observations':newpaths,'issues':issues,
        'scope':'Recomputation from stored source edges and present files; no independent Lean import parsing, --deps, object authentication, build, or dynamic ancestry.'}
out=here/'result.json';payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as f:f.write(payload)
elif sys.argv[1:]:raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=payload:raise SystemExit('result differs')
print(json.dumps({'status':result['status'],'issues':issues,'external_prefix_counts':result['external_prefix_counts']},sort_keys=True))
if issues:raise SystemExit(1)
