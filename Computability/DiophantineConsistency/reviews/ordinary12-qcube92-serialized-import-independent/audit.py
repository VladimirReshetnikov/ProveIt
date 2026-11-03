#!/usr/bin/env python3
"""Read-only reconstruction of the captured q-cube serialized-import scan."""
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
BASE=D/'research/ordinary12-sum-squares-model-bridge/observations/attempt01/terminal.json'
FILES={O/'result.json':'af847f4a3903770fd50bf7b7f09d597f748fa83ab0c3f4c0b7ae79dff192a615',
       O/'stdout':'d6a23d2beff9e51fa6edf8524cff0eb91d6106323dd20c4420ade0f69958ee8c',
       O/'stderr':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
       HERE/'scan.py':'381e344f1244afce06dfd97d0ff160f95d6d089a6c6a52a5ce86ca729b98c134'}
ATTEMPTS={'QCube92':'attempt05','QCube92Model':'model-attempt01',
          'FreeJRootBinding':'binding-attempt01','QCube92Existence':'existence-attempt03'}

def need(ok, msg):
    if not ok:raise SystemExit(msg)

def sha(p):return sha256(Path(p).read_bytes()).hexdigest()

def check_info(rec):
    p=Path(rec['path']);need(p.is_file() and str(p.resolve())==rec['realpath'] and sha(p)==rec['sha256'],'file drift: '+str(p))

def check_companions(base, observed):
    for suffix,record in observed.items():
        path=Path(str(base)[:-6]+suffix)
        if record is None:need(not path.is_file(),'new companion appeared: '+str(path))
        else:
            need(record['path']==str(path),'wrong companion path')
            check_info(record)

for f,h in FILES.items():need(sha(f)==h,'evidence pin mismatch: '+str(f))
r=json.loads((O/'result.json').read_text());inv=json.loads(INV.read_text());pre=json.loads(PRE.read_text());base=json.loads(BASE.read_text())
for file,h in r['pins'].items():need(sha(file)==h,'scan input changed: '+file)
need(r['exit']==0 and not (O/'stderr').read_bytes(),'reader did not exit cleanly')
need(r['preflight']['mem_available_kib']>=8*1024**2 and len(r['preflight']['lean'])<2,'resource guard mismatch')
need(len(r['preflight']['lean'])==0 and len(r['postflight']['lean'])==0,'observed overlap')
# Parse the exact reader output without relying on saved header dictionaries.
by_path={v['path']:name for name,v in r['objects'].items()};parsed={};current=None
for line in (O/'stdout').read_text().splitlines():
    if line.startswith('BEGIN '):
        need(current is None and line[6:] in by_path,'unexpected BEGIN')
        current=by_path[line[6:]];need(current not in parsed,'duplicate header');parsed[current]=[]
    elif line.startswith('IMPORT ') and current is not None:parsed[current].append(line[7:])
    elif line=='END' and current is not None:current=None
    else:raise SystemExit('unexpected reader output')
need(current is None and parsed==r['headers'] and set(parsed)==set(ATTEMPTS)|{'tail92','tail94'},'header record mismatch')
for rec in r['objects'].values():check_info(rec)
graph={name:list(imports) for name,imports in inv['imports'].items()};graph.update(pre['added_imports'])
for name in ATTEMPTS:graph[name]=parsed[name]
need(parsed['tail94']==graph['FreeJOrdinaryTailWitness'],'tail94 differs from stored headers')
need(parsed['tail92']==['Init','Init','FreeJSignedTransport'],'unexpected old tail imports')
need(parsed['tail94']==['Init','Init','DiophantineConsistency.FreeJSignedTransport'],'unexpected new tail imports')
summary={}
for root,attempt in ATTEMPTS.items():
    todo=deque([root]);seen=set();outside=set()
    while todo:
        name=todo.popleft()
        if name in seen or name in outside:continue
        if name not in graph:outside.add(name);continue
        seen.add(name);todo.extend(graph[name])
    row=r['roots'][root]
    need(seen==set(row['project_ancestors']) and outside==set(row['outside_graph']),'stored closure mismatch: '+root)
    need('FreeJOrdinaryTailWitness' not in seen and not row['tail_in_project_ancestry'],'tail reaches root: '+root)
    need({x.split('.')[0] for x in outside}<={'Foundation','Mathlib','Lean','Init'},'unexpected outside prefix')
    need(set(row['selected'])==seen-{root},'selected closure mismatch: '+root)
    receipt=json.loads((P/'observations'/attempt/'terminal.json').read_text());paths=receipt['lean_path'].split(':')[:-1]
    for name,selected in row['selected'].items():
        rel=name.replace('.','/')+'.olean'
        candidates=[Path(path)/rel for path in paths if (Path(path)/rel).is_file()]
        need(candidates and str(candidates[0])==selected['92']['path'],'first-resolved path mismatch: '+name)
        check_info(selected['92'])
        if name not in ATTEMPTS:
            rec=inv['objects'].get(name,pre['added_objects'].get(name))
            need(rec is not None and selected['92']['sha256']==rec['sha256'],'header object hash mismatch: '+name)
            need(rel in base['union'] and selected['92']['sha256']==base['union'][rel]['sha256'],'94 union hash mismatch: '+name)
            need(selected['94']['path']==base['union'][rel]['link'],'94 union path mismatch: '+name)
            check_info(selected['94'])
            for key,side,real in [('92_companions','92',False),('94_companions','94',False),
                                  ('92_real_companions','92',True),('94_real_companions','94',True)]:
                path=Path(selected[side]['realpath'] if real else selected[side]['path'])
                check_companions(path,selected[key])
        else:
            need(selected['92']['sha256']==r['objects'][name]['sha256'],'producer hash mismatch: '+name)
    summary[root]={'project':len(seen),'outside':len(outside),'tail_ancestor':False}
for side in ('92','94'):
    rec=r['objects']['tail'+side];check_companions(Path(rec['path']),r['tail_companions'][side])
old_source=Path(r['tail_companions']['92']['.lean']['path']).read_text().splitlines()
new_source=Path(r['tail_companions']['94']['.lean']['path']).read_text().splitlines()
need(old_source[0]=='import FreeJSignedTransport' and new_source[0]=='import DiophantineConsistency.FreeJSignedTransport' and old_source[1:]==new_source[1:],'tail source difference changed')
for file,h in r['pins'].items():need(sha(file)==h,'scan input changed during review: '+file)
for f,h in FILES.items():need(sha(f)==h,'evidence changed during review: '+str(f))
print(json.dumps({'roots':summary,'selected_94_project_hashes':'PASS',
                  'tail_source_difference':'one import line','recorded_companions':'PASS'},indent=2))
