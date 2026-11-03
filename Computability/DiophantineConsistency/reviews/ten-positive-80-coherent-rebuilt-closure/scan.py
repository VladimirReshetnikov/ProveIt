#!/usr/bin/env python3
"""Read every selected project header from the completed fresh 80 union."""
from collections import deque
from hashlib import sha256
from pathlib import Path
import json,subprocess,sys,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
ATT=D/'research/ten-positive-80-coherent-rebuild/observations/attempt04'
OUTER=D/'research/ten-positive-80-coherent-rebuild/observations/outer-attempt04/terminal.json'
OLD=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
BASE=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
HELPER=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');O=H/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def sample():
 rows=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
 ps=[x.strip() for x in rows if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean']
 mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])
 return {'time_ns':time.time_ns(),'lean':ps,'mem_available_kib':mem}
def comp(stem,template):
 result={}
 for suffix,old in template.items():
  p=Path(str(stem)+suffix);need(p.is_file()==(old is not None),'companion presence '+str(p))
  if old is None:result[suffix]=None
  else:
   h=sha(p);need(h==old['sha256'],'companion hash '+str(p))
   result[suffix]={'path':str(p),'real_path':str(p.resolve(strict=True)),'sha256':h}
 return result
need(not O.exists(),'observation exists')
need(sha(ATT/'result.json')=='e1ccee0f9c5fdc14cde89368925cb56f41d6acbe5c89a41c9e2bab798184582b','replay result drift')
need(sha(OUTER)=='6d385d6ced237bedd626daabc047691d49a5314f399b941d3a09c1f71cc9aa96','outer receipt drift')
need(sha(OLD)=='d65d7c776eb23425f9e2a290d8c3fdeebc011920619241290fdee85bc4ae68a9','old scan drift')
need(sha(BASE)=='09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed','base inventory drift')
need(sha(HELPER)=='886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f','helper drift')
run=json.loads((ATT/'result.json').read_text());outer=json.loads(OUTER.read_text());old=json.loads(OLD.read_text());base=json.loads(BASE.read_text())
need(run['status']=='PASS' and outer['exit']==0 and outer['runner_sha256_before']==outer['runner_sha256_after']=='1956a0831c4dc93c5f30ff578ec6e7731c7d56f4be695d3ee8a7c4681a982298','run status')
need(sha(ATT/'initial-project.json')==run['initial_project_sha256'] and sha(ATT/'outside-baseline.json')==run['outside_baseline_sha256'],'baseline drift')
initial=json.loads((ATT/'initial-project.json').read_text()); outside=json.loads((ATT/'outside-baseline.json').read_text());built=run['built']
need(len(initial)==1765 and len(built)==127 and len(outside)==80,'inventory size')
union=Path(run['output_root'])/'lib';need(union.is_dir(),'union missing')
names=sorted(initial);expected={n:(built[n] if n in built else initial[n]) for n in names}
prior=base['post_headers']['project']; reference={n:prior[n]['imports'] for n in names if n in prior};reference.update(old['fresh_headers'])
need(set(reference)==set(names),'expected header graph incomplete')
inputs={str(p):sha(p) for p in (ATT/'result.json',OUTER,OLD,BASE,HELPER,LEAN,H/'scan.py',ATT/'initial-project.json',ATT/'outside-baseline.json')}
pre=sample();need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'resource preflight')
O.mkdir(parents=True); selected={n:comp(union/n.replace('.','/'),expected[n]) for n in names}
outside_now={}
for n,template in outside.items():
 obj=template['.olean'];need(obj is not None,'missing outside object '+n)
 outside_now[n]=comp(Path(obj['path'][:-6]),template)
 need(not (union/(n.replace('.','/')+'.olean')).is_file(),'outside shadowed by project '+n)
headers={}; batches=[]
for k in range(0,len(names),64):
 chunk=names[k:k+64];paths=[str(union/(n.replace('.','/')+'.olean')) for n in chunk];mapping=dict(zip(paths,chunk))
 guard=sample();need(guard['mem_available_kib']>=8*1024**2 and len(guard['lean'])<2,'resource batch guard')
 cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER),*paths]
 start=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True,timeout=120);end=sample()
 (O/f'header-{k//64:03}.stdout').write_text(r.stdout);(O/f'header-{k//64:03}.stderr').write_text(r.stderr)
 need(r.returncode==0 and not r.stderr,'header reader failed')
 cur=None;batch={}
 for line in r.stdout.splitlines():
  if line.startswith('BEGIN '):
   need(cur is None and line[6:] in mapping,'unexpected begin');cur=mapping[line[6:]];need(cur not in batch,'duplicate begin');batch[cur]=[]
  elif line.startswith('IMPORT ') and cur is not None:batch[cur].append(line[7:])
  elif line=='END' and cur is not None:cur=None
  else:raise RuntimeError('malformed header')
 need(cur is None and set(batch)==set(chunk),'missing header')
 for n,imports in batch.items():need(imports==reference[n],'header changed '+n)
 headers.update(batch);batches.append({'command':cmd,'exit':r.returncode,'elapsed':time.monotonic()-start,'preflight':guard,'postflight':end})
need(set(headers)==set(names),'incomplete headers')
todo=deque(['Direct80SymbolicFixedIPRA']);seen=set();ext=set()
while todo:
 n=todo.popleft()
 if n in seen or n in ext:continue
 if n not in headers:ext.add(n);continue
 seen.add(n);todo.extend(headers[n])
need(seen==set(names) and ext==set(outside),'selected closure differs from captured inventory')
for n in names:need(comp(union/n.replace('.','/'),expected[n])==selected[n],'project drift '+n)
for n,template in outside.items():need(comp(Path(template['.olean']['path'][:-6]),template)==outside_now[n],'outside drift '+n)
for p,h in inputs.items():need(sha(p)==h,'input drift '+p)
result={'status':'PASS','inputs':inputs,'union':str(union),'selected_project':selected,'selected_outside':outside_now,
 'headers':headers,'batches':batches,'preflight':pre,'postflight':sample(),
 'scope':'actual serialized headers for all selected project objects and selected companion files; unrebuilt historical project source-object, outside transitive and dynamic provenance inherited'}
(O/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','project':len(seen),'outside':len(ext),'batches':len(batches),'sha256':sha(O/'result.json')},sort_keys=True))
