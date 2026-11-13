#!/usr/bin/env python3
"""Guarded read of six .olean import headers and selected-project ancestry."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import time

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
P = D/'research/ordinary12-qcube92-candidate'
B = D/'research/ordinary12-ipra-bridge'
INV = B/'compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
PRE = D/'research/ordinary12-sum-squares-endpoint-import-preflight/observations/attempt02/result.json'
BASE = D/'research/ordinary12-sum-squares-model-bridge/observations/attempt01/terminal.json'
HELPER = B/'compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OBS = HERE/'observations/attempt01'
FIXED = {INV:'bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2',
         PRE:'b15febdf3f77edc4ecdabddb3da2d9bf8735549d28869c4ec18d0669096a45ce',
         BASE:'febe3f4317dd62fa24d0194844490350f08db1176705a6ebf6db08119efba580',
         HELPER:'886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f'}
ROOTS = {'QCube92':'attempt05', 'QCube92Model':'model-attempt01',
         'FreeJRootBinding':'binding-attempt01', 'QCube92Existence':'existence-attempt03'}

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def resource():
    ps = subprocess.run(['ps','-eo','pid=,comm=,rss=,args='], capture_output=True, text=True, check=True).stdout
    procs=[]
    for line in ps.splitlines():
        f=line.strip().split(None,3)
        if len(f)==4 and f[1]=='lean':
            procs.append({'pid':int(f[0]), 'rss_kib':int(f[2]), 'args':f[3]})
    mem=next(line for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
    return {'time_ns':time.time_ns(), 'mem_available_kib':int(mem.split()[1]), 'lean':procs}

def info(path):
    path=Path(path)
    return {'path':str(path), 'realpath':str(path.resolve(strict=True)), 'sha256':digest(path)}

def companions(path):
    path=Path(path)
    need(str(path).endswith('.olean'), 'not an olean')
    result={}
    for suffix in ('.lean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.ilean.hash'):
        candidate=Path(str(path)[:-6]+suffix)
        result[suffix]=info(candidate) if candidate.is_file() else None
    return result

need(not OBS.exists(), 'refusing to overwrite scan')
for path, value in FIXED.items():
    need(digest(path)==value,'fixed input hash mismatch: '+str(path))
inv=json.loads(INV.read_text()); pre=json.loads(PRE.read_text()); base=json.loads(BASE.read_text())
need(inv['complete'] and inv['overlay_unchanged'] and inv['omitted_unchanged'], 'prior inventory incomplete')
need(base['exit_code']==0 and base['union_unchanged'] and base['guards_unchanged'], '94 model manifest incomplete')
files={}; receipts={}; pins={str(k):digest(k) for k in FIXED}; pins[str(LEAN)]=digest(LEAN); pins[str(HERE/'scan.py')]=digest(HERE/'scan.py')
for name, attempt in ROOTS.items():
    rp=P/'observations'/attempt/'terminal.json'; r=json.loads(rp.read_text()); source=P/(name+'.lean')
    need(r['exit']==0 and not r['reason'] and r['before']==r['after'] and r['selected_provider_unchanged'], 'bad producer receipt: '+name)
    need(r['before'][str(source)]==digest(source),'source pin mismatch: '+name)
    path=Path(r['output_root'])/(name+'.olean')
    need(path.is_file() and digest(path)==r['object_sha256'],'object pin mismatch: '+name)
    files[name]=path;receipts[name]=r
    for f in (rp,source,path):pins[str(f)]=digest(f)
tail_old=Path('/tmp/free-j-ordinary-tail-witness-author-cdbrbrco/FreeJOrdinaryTailWitness.olean')
tail_new=Path('/tmp/free-j-namespaced-client-author-3wobi3_d/FreeJOrdinaryTailWitness.olean')
need(digest(tail_old)=='b36cc3c0c13c6aba7538ec3587933b816907706432cb38d8419391f8799474fe', 'unnamespaced tail drift')
need(digest(tail_new)=='3af9bb5c54c1fda2d7ea0daf22e43c4fe02176b5eda32a345b45ded73024304e','namespaced tail drift')
files['tail92']=tail_old; files['tail94']=tail_new
for f in (tail_old,tail_new):pins[str(f)]=digest(f)
need(len({str(v) for v in files.values()})==6,'duplicate reader paths')
initial=resource();need(initial['mem_available_kib']>=8*1024**2 and len(initial['lean'])<2,'resource guard refused')
OBS.mkdir(parents=True)
cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER),*[str(p) for p in files.values()]]
t0=time.monotonic(); proc=subprocess.run(cmd,capture_output=True,text=True,timeout=60);elapsed=time.monotonic()-t0;post=resource()
(OBS/'stdout').write_text(proc.stdout);(OBS/'stderr').write_text(proc.stderr)
need(proc.returncode==0 and not proc.stderr,'header reader failed')
by_path={str(v):k for k,v in files.items()};headers={};current=None
for line in proc.stdout.splitlines():
    if line.startswith('BEGIN '):
        need(current is None and line[6:] in by_path,'unexpected BEGIN')
        current=by_path[line[6:]];need(current not in headers,'duplicate header');headers[current]=[]
    elif line.startswith('IMPORT ') and current is not None:headers[current].append(line[7:])
    elif line=='END' and current is not None:current=None
    else:raise RuntimeError('unexpected header line: '+line)
need(current is None and set(headers)==set(files),'incomplete headers')
graph={k:list(v) for k,v in inv['imports'].items()};graph.update(pre['added_imports'])
for name in ROOTS:graph[name]=headers[name]
results={}
for root in ROOTS:
    seen=set();outside=set();todo=[root]
    while todo:
        name=todo.pop()
        if name in seen or name in outside:continue
        if name not in graph:outside.add(name);continue
        seen.add(name);todo.extend(graph[name])
    need('FreeJOrdinaryTailWitness' not in seen,'conflicting tail is in project closure')
    selected={}; localroots=receipts[root]['lean_path'].split(':')[:-1]
    for name in sorted(seen):
        if name in ROOTS:
            # A selected dependency must resolve to the same producer bytes.
            rel=name+'.olean'; expected=digest(files[name])
            candidates=[Path(r)/rel for r in localroots if (Path(r)/rel).is_file()]
            if name==root:
                need(not candidates or digest(candidates[0])==expected,'root shadow mismatch')
                continue
        else:
            rel=name.replace('.','/')+'.olean'; rec=inv['objects'].get(name,pre['added_objects'].get(name))
            need(rec is not None,'missing stored header record: '+name);expected=rec['sha256']
            candidates=[Path(r)/rel for r in localroots if (Path(r)/rel).is_file()]
        need(candidates,'no selected project object: '+name)
        p=candidates[0];need(digest(p)==expected,'selected object does not match stored header: '+name)
        if name not in ROOTS:
            need(rel in base['union'] and base['union'][rel]['sha256']==expected,'94 model object differs: '+name)
            path94=Path(base['union'][rel]['link'])
            selected[name]={'92':info(p),'94':info(path94),
                            '92_companions':companions(p), '94_companions':companions(path94),
                            '92_real_companions':companions(p.resolve()),'94_real_companions':companions(path94.resolve())}
        else:selected[name]={'92':info(p)}
    results[root]={'project_ancestors':sorted(seen),'outside_graph':sorted(outside),'selected':selected,
                   'tail_in_project_ancestry':False}
need(headers['tail94']==graph['FreeJOrdinaryTailWitness'],'94 tail header differs from prior inventory')
need(base['union']['FreeJOrdinaryTailWitness.olean']['sha256']==digest(tail_new),'94 tail differs from base manifest')
need(digest(tail_old)!=digest(tail_new),'expected tail conflict absent')
for path,value in pins.items():need(digest(Path(path))==value,'pinned input changed during scan: '+path)
for entry in results.values():
    for selected in entry['selected'].values():
        for side in ('92','94'):
            if side in selected:
                file=Path(selected[side]['path']);need(info(file)==selected[side],'selected object changed during scan')
for path in (tail_old,tail_new):
    for rec in companions(path).values():
        if rec is not None:need(info(rec['path'])==rec,'tail companion changed')
result={'pins':pins,'command':cmd,'exit':proc.returncode,'elapsed':elapsed,'preflight':initial,'postflight':post,
        'objects':{k:info(v) for k,v in files.items()},'headers':headers,'roots':results,
        'tail_companions':{'92':companions(tail_old),'94':companions(tail_new)},
        'scope':'Selected serialized project header ancestry; inherited header inventory and package-transitive/dynamic ancestry.'}
(OBS/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'exit':proc.returncode,'roots':{k:{'project':len(v['project_ancestors']),'outside':len(v['outside_graph']),'tail':v['tail_in_project_ancestry']} for k,v in results.items()},'tail_hashes':[digest(tail_old),digest(tail_new)],'elapsed':elapsed},indent=2))
