#!/usr/bin/env python3
"""Check serialized namespaced replacement and selected-project closure."""
from collections import deque
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import time

if sys.flags.optimize:raise SystemExit('optimized Python refused')
HERE=Path(__file__).resolve().parent
D=HERE.parents[1]
P=D/'research/ordinary12-qcube92-candidate'
OLD=D/'reviews/ordinary12-qcube92-serialized-import-independent/observations/attempt01/result.json'
INV=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
PRE=D/'research/ordinary12-sum-squares-endpoint-import-preflight/observations/attempt02/result.json'
HELPER=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
O=HERE/'observations/attempt01'
N=P/'observations/namespaced-attempt01/terminal.json'
H=P/'observations/halt-attempt01/terminal.json'
FIXED={OLD:'af847f4a3903770fd50bf7b7f09d597f748fa83ab0c3f4c0b7ae79dff192a615',
       INV:'bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2',
       PRE:'b15febdf3f77edc4ecdabddb3da2d9bf8735549d28869c4ec18d0669096a45ce',
       HELPER:'886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f',
       N:'ba2339744d0ed01acca10754dc56f9967d628292bf0ddd6b3a8350a1d71e4f01',
       H:'4e04eaa339d336845538c3ebe30fecc1ff233c2b9bd54ad1fd7e2c1080534764',
       P/'QCube92NamespacedExistence.lean':'5b47d82b5ad78815983773588bb6c9822b6646ae0a6595a600b7f639f424c81a',
       P/'QCube92Existence.lean':'62b030d3c8d0ccfac46b4b0c41be58c67dbe96e7794d01c284c317499c456e9d',
       P/'observations/halt-attempt01/stdout':'fd01406bde2292141145559de00a9f56aa24c33bdd7aae6eb22bf26e1bd65498',
       P/'observations/namespaced-attempt01/stdout':'cdc784b526f09d2793f6541485070a05be709d088e62dfb11e06b81d965fa29c'}

def need(x,msg):
    if not x:raise RuntimeError(msg)

def sha(p):return sha256(Path(p).read_bytes()).hexdigest()

def sample():
    ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout
    rows=[]
    for line in ps.splitlines():
        f=line.strip().split(None,3)
        if len(f)==4 and f[1]=='lean':rows.append({'pid':int(f[0]),'rss_kib':int(f[2]),'args':f[3]})
    m=next(s for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:'))
    return {'time_ns':time.time_ns(),'mem_available_kib':int(m.split()[1]),'lean':rows}

need(not O.exists(),'refusing to overwrite observation')
for p,h in FIXED.items():need(sha(p)==h,'input hash mismatch: '+str(p))
n=json.loads(N.read_text());h=json.loads(H.read_text());old=json.loads(OLD.read_text());inv=json.loads(INV.read_text());pre=json.loads(PRE.read_text())
need(n['exit']==0 and not n['reason'] and n['base_unchanged'] and n['extra_unchanged'] and n['union_unchanged'],'namespaced producer failed')
need(h['exit']!=0 and 'environment already contains' in (P/'observations/halt-attempt01/stdout').read_text(),'expected collision not captured')
need(h['union']==n['union'] and n['union_count']==1292,'halt/namespaced union changed')
oldsrc=(P/'QCube92Existence.lean').read_text();newsrc=(P/'QCube92NamespacedExistence.lean').read_text()
need(oldsrc.replace('import FreeJRootBinding\n','import DiophantineConsistency.FreeJRootBinding\n').replace('FreeJQCube92Existence','FreeJQCube92NamespacedExistence')==newsrc,'unexpected source rewrite')
obj=Path(n['output_root'])/'QCube92NamespacedExistence.olean'; binding=Path(n['union']['DiophantineConsistency/FreeJRootBinding.olean']['resolved'])
need(sha(obj)==n['object_sha256']=='39c9aaf5b87e85a224b281fdeb7714a64120693ef8799e45a5a9f8efa2a40ec0','namespaced object mismatch')
need(sha(binding)==n['union']['DiophantineConsistency/FreeJRootBinding.olean']['sha256']=='58860b9c6f256a15df038991edc682af4b4c831ab0ae3c3565f1f14ea4833b40','binding object mismatch')
pins={str(p):sha(p) for p in list(FIXED)+[LEAN,HERE/'scan.py',obj,binding]}
initial=sample();need(initial['mem_available_kib']>=8*1024**2 and len(initial['lean'])<2,'resource guard refused')
O.mkdir(parents=True)
cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER),str(obj),str(binding)]
t0=time.monotonic();proc=subprocess.run(cmd,capture_output=True,text=True,timeout=60);elapsed=time.monotonic()-t0;post=sample()
(O/'stdout').write_text(proc.stdout);(O/'stderr').write_text(proc.stderr)
need(proc.returncode==0 and not proc.stderr,'header reader failed')
headers={};current=None;by_path={str(obj):'QCube92NamespacedExistence',str(binding):'DiophantineConsistency.FreeJRootBinding'}
for line in proc.stdout.splitlines():
    if line.startswith('BEGIN '):
        need(current is None and line[6:] in by_path,'unexpected BEGIN');current=by_path[line[6:]];need(current not in headers,'duplicate header');headers[current]=[]
    elif line.startswith('IMPORT ') and current is not None:headers[current].append(line[7:])
    elif line=='END' and current is not None:current=None
    else:raise RuntimeError('unexpected reader output')
need(current is None and set(headers)==set(by_path.values()),'incomplete headers')
need(headers['QCube92NamespacedExistence']==['Init','Init','QCube92Model','DiophantineConsistency.FreeJRootBinding'],'unexpected serialized namespaced imports')
graph={k:list(v) for k,v in inv['imports'].items()};graph.update(pre['added_imports'])
for name in ('QCube92','QCube92Model','FreeJRootBinding','QCube92Existence'):graph[name]=old['headers'][name]
need(headers['DiophantineConsistency.FreeJRootBinding']==graph['DiophantineConsistency.FreeJRootBinding'],'namespaced binding header differs from inventory')
graph.update(headers)
results={}
for root in ('QCube92NamespacedExistence','CompactBytePortsModelIff','CompactSymbolicModelUnconditionalIff'):
    todo=deque([root]);seen=set();outside=set()
    while todo:
        name=todo.popleft()
        if name in seen or name in outside:continue
        if name not in graph:outside.add(name);continue
        seen.add(name);todo.extend(graph[name])
    need('FreeJRootBinding' not in seen,'top-level duplicate is an ancestor: '+root)
    need('DiophantineConsistency.FreeJRootBinding' in seen,'namespaced binding absent from closure: '+root)
    checked={}
    for name in sorted(seen):
        if name=='QCube92NamespacedExistence':continue
        rel=name.replace('.','/')+'.olean';need(rel in n['union'],'module absent from selected union: '+name)
        record=n['union'][rel];path=Path(record['link']);need(path.is_file() and sha(path)==record['sha256'],'selected union object drift: '+name)
        if name in ('QCube92','QCube92Model'):
            expected=old['objects'][name]['sha256']
        else:
            prev=inv['objects'].get(name,pre['added_objects'].get(name));need(prev is not None,'missing captured header: '+name);expected=prev['sha256']
        need(expected==record['sha256'],'selected object differs from captured header: '+name)
        checked[name]={'path':str(path),'realpath':str(path.resolve()),'sha256':record['sha256']}
    results[root]={'project_ancestors':sorted(seen),'outside_graph':sorted(outside),'selected':checked,
                   'top_level_binding_ancestor':False,'namespaced_binding_ancestor':True}
for p,v in pins.items():need(sha(p)==v,'input changed during scan: '+p)
for result in results.values():
    for item in result['selected'].values():need(sha(item['path'])==item['sha256'] and str(Path(item['path']).resolve())==item['realpath'],'selected object changed during scan')
record={'pins':pins,'command':cmd,'exit':proc.returncode,'elapsed':elapsed,'preflight':initial,'postflight':post,
        'object':{'path':str(obj),'sha256':sha(obj)},'binding':{'path':str(binding),'sha256':sha(binding)},
        'headers':headers,'roots':results,'scope':'selected serialized-project ancestry; inherited package/dynamic and source-object ancestry'}
(O/'result.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps({'exit':proc.returncode,'roots':{k:{'project':len(v['project_ancestors']),'outside':len(v['outside_graph'])} for k,v in results.items()},'elapsed':elapsed},indent=2))
