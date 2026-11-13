#!/usr/bin/env python3
"""Recheck captured namespaced headers, prior collision and project ancestry."""
from collections import deque
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
D=HERE.parents[1]
P=D/'research/ordinary12-qcube92-candidate'
O=HERE/'observations/attempt01'
INV=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
PRE=D/'research/ordinary12-sum-squares-endpoint-import-preflight/observations/attempt02/result.json'
OLD=D/'reviews/ordinary12-qcube92-serialized-import-independent/observations/attempt01/result.json'
N=P/'observations/namespaced-attempt01/terminal.json'
H=P/'observations/halt-attempt01/terminal.json'
FILES={O/'result.json':'d3f68298e20708297524c0e0e540091e184d451972fdb801ab9081c227779934',
       O/'stdout':'e1afe56caf56d860bc1e68d973da743d213a7f2782c60e1e4c9a69641647e29c',
       O/'stderr':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
       HERE/'scan.py':'1fde5745d37162ef427ed6a9762cf2d7b7175e0d207784866a2f318027a1cfd9'}

def need(x,msg):
    if not x:raise SystemExit(msg)

def sha(p):return sha256(Path(p).read_bytes()).hexdigest()

for f,h in FILES.items():need(sha(f)==h,'evidence pin mismatch: '+str(f))
r=json.loads((O/'result.json').read_text());n=json.loads(N.read_text());h=json.loads(H.read_text());old=json.loads(OLD.read_text());inv=json.loads(INV.read_text());pre=json.loads(PRE.read_text())
for p,v in r['pins'].items():need(sha(p)==v,'scan input changed: '+p)
need(r['exit']==0 and not (O/'stderr').read_bytes(),'header reader failure')
need(r['preflight']['mem_available_kib']>=8*1024**2 and len(r['preflight']['lean'])<2,'resource guard mismatch')
need(len(r['preflight']['lean'])==len(r['postflight']['lean'])==0,'recorded Lean overlap')
oldsrc=(P/'QCube92Existence.lean').read_text();newsrc=(P/'QCube92NamespacedExistence.lean').read_text()
need(oldsrc.replace('import FreeJRootBinding\n','import DiophantineConsistency.FreeJRootBinding\n').replace('FreeJQCube92Existence','FreeJQCube92NamespacedExistence')==newsrc,'source rewrite mismatch')
need(h['exit']!=0 and n['exit']==0 and h['union']==n['union'] and n['union_count']==1292,'compile records mismatch')
need("environment already contains 'FreeJRootBinding.rhs' from FreeJRootBinding" in (P/'observations/halt-attempt01/stdout').read_text(),'collision diagnostic mismatch')
need(n['base_unchanged'] and n['extra_unchanged'] and n['union_unchanged'],'namespaced author guards failed')
output=Path(n['output_root'])/'QCube92NamespacedExistence.olean'
need(sha(output)==n['object_sha256']==r['object']['sha256'] and str(output)==r['object']['path'],'namespaced object drift')
need(sha(Path(n['output_root'])/'QCube92NamespacedExistence.lean')==n['source_sha256']==n['source_after'],'namespaced source snapshot drift')
need(sha(P/'observations/namespaced-attempt01/stdout')==n['stdout_sha256'] and sha(P/'observations/namespaced-attempt01/stderr')==n['stderr_sha256'],'namespaced logs drift')
expected="'FreeJQCube92NamespacedExistence.transform_positive' depends on axioms: [propext, Classical.choice, Quot.sound]\n'FreeJQCube92NamespacedExistence.positive_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
need((P/'observations/namespaced-attempt01/stdout').read_text()==expected and not (P/'observations/namespaced-attempt01/stderr').read_bytes(),'unexpected namespaced log')
# Independently reconstruct the two newly captured object headers.
path_map={r['object']['path']:'QCube92NamespacedExistence',r['binding']['path']:'DiophantineConsistency.FreeJRootBinding'}
parsed={};current=None
for line in (O/'stdout').read_text().splitlines():
    if line.startswith('BEGIN '):
        need(current is None and line[6:] in path_map,'unexpected BEGIN')
        current=path_map[line[6:]];need(current not in parsed,'duplicate header');parsed[current]=[]
    elif line.startswith('IMPORT ') and current is not None:parsed[current].append(line[7:])
    elif line=='END' and current is not None:current=None
    else:raise SystemExit('unexpected header output')
need(current is None and parsed==r['headers'] and set(parsed)==set(path_map.values()),'captured headers differ')
need(parsed['QCube92NamespacedExistence']==['Init','Init','QCube92Model','DiophantineConsistency.FreeJRootBinding'],'wrong namespaced imports')
need(sha(r['binding']['path'])==r['binding']['sha256']=='58860b9c6f256a15df038991edc682af4b4c831ab0ae3c3565f1f14ea4833b40','binding object drift')
graph={k:list(v) for k,v in inv['imports'].items()};graph.update(pre['added_imports'])
for name in ('QCube92','QCube92Model','FreeJRootBinding','QCube92Existence'):graph[name]=old['headers'][name]
need(parsed['DiophantineConsistency.FreeJRootBinding']==graph['DiophantineConsistency.FreeJRootBinding'],'binding prior header mismatch')
graph.update(parsed)
summary={}
for root,record in r['roots'].items():
    todo=deque([root]);seen=set();outside=set()
    while todo:
        name=todo.popleft()
        if name in seen or name in outside:continue
        if name not in graph:outside.add(name);continue
        seen.add(name);todo.extend(graph[name])
    need(seen==set(record['project_ancestors']) and outside==set(record['outside_graph']),'closure mismatch: '+root)
    need('FreeJRootBinding' not in seen and 'QCube92Existence' not in seen and 'DiophantineConsistency.FreeJRootBinding' in seen,'unexpected module reachability: '+root)
    expected_names=seen-({'QCube92NamespacedExistence'} if root=='QCube92NamespacedExistence' else set())
    need(set(record['selected'])==expected_names,'selected set mismatch: '+root)
    for name,entry in record['selected'].items():
        rel=name.replace('.','/')+'.olean';need(rel in n['union'],'missing union module: '+name)
        u=n['union'][rel];path=Path(entry['path'])
        need(entry['path']==u['link'] and entry['sha256']==u['sha256'] and str(path.resolve())==entry['realpath'] and sha(path)==entry['sha256'],'union object mismatch: '+name)
        reference=old['objects'][name] if name in ('QCube92','QCube92Model') else inv['objects'].get(name,pre['added_objects'].get(name))
        need(reference is not None and entry['sha256']==reference['sha256'],'captured header object mismatch: '+name)
    summary[root]={'project':len(seen),'outside':len(outside),'old_top_level_modules':False}
for p,v in r['pins'].items():need(sha(p)==v,'scan input changed during review: '+p)
for f,v in FILES.items():need(sha(f)==v,'scan evidence changed during review: '+str(f))
print(json.dumps({'roots':summary,'same_union_failed_vs_namespaced':True,'recorded_duplicate_import_avoided':True},indent=2))
