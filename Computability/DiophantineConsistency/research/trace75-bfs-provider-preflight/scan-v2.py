#!/usr/bin/env python3
"""Inspect the selected serialized project ancestry of the planned trace75/BFS carry union."""
from collections import deque
from hashlib import sha256
from pathlib import Path
import json, os, re, subprocess, sys, time, traceback
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent; D=H.parents[1]
BFS=D/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json'
TRACE=D/'research/trace75-root-probe/observations/fixedcongruence-attempt01/terminal.json'
HELPER=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
UNION=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib'); PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
CORE=LEAN.parent.parent/'lib/lean'; LIB=Path('/tmp/direct90-ipra-join-b66u_qqo/lib')
O=H/'observations/scan-attempt01'
PINS={BFS:'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',TRACE:'62bed210c2f1c7af9dc82deb24b55a5c5f0a1717f0a7211d06137821e2553eeb',HELPER:'886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
ROOTS={'Trace75FixedCongruence':'c0f5362c02d9eb09f731d3a7c5ff178407991c8c252c2a57e23794084804a930','DirectBFSBandCarry':'e585f2a52aece195858cdfcbcbe764df2aa8984af9cbebdd018e97a7b1e51e7e'}
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash']
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def sample():
 rows=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
 lean=[s.strip() for s in rows if len(s.split(None,3))==4 and s.split(None,3)[1]=='lean']
 mem=int(next(s for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')).split()[1])
 return {'time_ns':time.time_ns(),'lean':lean,'mem_available_kib':mem}
def guard():
 x=sample();need(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<2,'resource preflight');return x
def rec(p):
 if not os.path.lexists(p):return None
 need(p.is_file(),'not a file '+str(p));return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
def bundle(p):
 stem=str(p)[:-6];return {s:rec(Path(stem+s)) for s in SUFFIXES}
def selected(name,paths):
 need(re.fullmatch(r'[A-Za-z0-9_\.]+',name) is not None,'invalid module name '+name)
 rel=Path(*name.split('.')).with_suffix('.olean')
 for root in paths:
  p=root/rel
  if os.path.lexists(p):
   need(p.is_file(),'dangling or non-file shadow '+str(p));return p
 return None
def is_external(p):
 return p.is_relative_to(PACK) or p.is_relative_to(CORE)
def parse(out,mapping):
 got={};cur=None
 for line in out.splitlines():
  if line.startswith('BEGIN '):
   need(cur is None and line[6:] in mapping,'bad begin');cur=mapping[line[6:]];need(cur not in got,'repeated begin');got[cur]=[]
  elif line.startswith('IMPORT ') and cur is not None:got[cur].append(line[7:])
  elif line=='END' and cur is not None:cur=None
  else:raise RuntimeError('malformed header line '+line)
 need(cur is None and set(got)==set(mapping.values()),'missing or incomplete header');return got
need(not O.exists(),'observation exists')
RUNNER_SHA=sha(__file__)
for p,h in PINS.items():need(sha(p)==h,'input drift '+str(p))
base=json.loads(BFS.read_text());tr=json.loads(TRACE.read_text());need(base['status']=='PASS' and tr['exit']==0 and tr['reason'] is None,'bad producer status')
prior=base['closure']['project']; roots=[Path(x) for x in tr['lean_path'].split(':')];need(LIB in roots and PACK in roots,'missing terminal paths')
roots.insert(0,Path(tr['output_root']));roots.insert(roots.index(LIB),UNION);roots.append(CORE)
env={'PATH':'/usr/bin:/bin'}
pre=guard();O.mkdir(parents=True); (O/'search-path.json').write_text(json.dumps([str(x) for x in roots],indent=2)+'\n')
selected_objects={};headers={};external={};unresolved=[]; batches=[]; reused=[]; queue=deque(ROOTS); processed=set();failure=None
try:
 while queue:
  frontier=[]
  while queue and len(frontier)<32:
   n=queue.popleft()
   if n in processed:continue
   processed.add(n);p=selected(n,roots)
   if p is None:unresolved.append(n);continue
   snap=bundle(p)
   if is_external(p):external[n]=snap;continue
   selected_objects[n]=snap
   if n in ROOTS:need(snap['.olean']['sha256']==ROOTS[n],'root hash drift '+n)
   old=prior.get(n)
   if old is not None and old['record']['sha256']==snap['.olean']['sha256']:
    headers[n]=old['imports'];reused.append(n);queue.extend(headers[n])
   else:frontier.append((n,p))
  if not frontier:continue
  before=guard();cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER)]+[str(p) for _,p in frontier]
  k=len(batches);out=O/f'header-{k:03}.stdout';err=O/f'header-{k:03}.stderr'
  start=time.monotonic();samples=[];reason=None
  with out.open('x') as out_f,err.open('x') as err_f:
   proc=subprocess.Popen(cmd,stdout=out_f,stderr=err_f,text=True,env=env)
   try:
    while proc.poll() is None:
     time.sleep(0.25);snap=sample();samples.append(snap)
     if snap['mem_available_kib']<8*1024**2 or len(snap['lean'])>2:reason='resource guard';proc.kill();break
     if time.monotonic()-start>45:reason='timeout';proc.kill();break
   finally:
    if proc.poll() is None:proc.kill()
    proc.wait()
  stdout=out.read_text();stderr=err.read_text()
  batches.append({'command':cmd,'env':env,'exit':proc.returncode,'reason':reason,'preflight':before,'samples':samples,'postflight':sample(),'stdout_sha256':sha(out),'stderr_sha256':sha(err)})
  need(reason is None and proc.returncode==0 and not stderr,'header reader failed')
  parsed=parse(stdout,{str(p):n for n,p in frontier});headers.update(parsed)
  for v in parsed.values():queue.extend(v)
 need(not unresolved,'unresolved modules: '+repr(unresolved))
 def closure(root):
  seen=set();out=set();todo=[root]
  while todo:
   n=todo.pop()
   if n in seen or n in out:continue
   if n not in headers:out.add(n);continue
   seen.add(n);todo.extend(headers[n])
  return seen,out
 details={};five=['DiophantineConsistency.ModelRatioBounds','DiophantineConsistency.ArithmeticNegativeNorms','DiophantineConsistency.ArithmeticCarrierRadix2011','DiophantineConsistency.ArithmeticWindowInterface','DiophantineConsistency.ArithmeticCarrierSoundness2011']
 for root in ROOTS:
  seen,out=closure(root);need(out<=set(external),'unresolved closure '+root)
  details[root]={'project':sorted(seen),'outside':sorted(out),'five_overlap_names':{n:n in seen for n in five}}
 bfsseen=set(details['DirectBFSBandCarry']['project']);conflicts={};companion_conflicts={};missing=[]
 for n in sorted(bfsseen):
  old=prior.get(n)
  if old is None:missing.append(n)
  else:
   if old['record']['sha256']!=selected_objects[n]['.olean']['sha256']:conflicts[n]={'prior':old['record']['sha256'],'selected':selected_objects[n]['.olean']['sha256']}
   for suffix in SUFFIXES:
    a=old['companions'].get(suffix);b=selected_objects[n][suffix]
    ah=None if a is None else a['sha256'];bh=None if b is None else b['sha256']
    if ah!=bh:companion_conflicts.setdefault(n,{})[suffix]={'prior':ah,'selected':bh}
 for n,snap in list(selected_objects.items())+list(external.items()):
  original=Path(snap['.olean']['path']);need(selected(n,roots)==original,'first-selected path changed '+n)
  need(bundle(original)==snap,'selected companion drift '+n)
 for p,h in PINS.items():need(sha(p)==h,'post-input drift '+str(p))
 need(sha(__file__)==RUNNER_SHA,'scanner drift')
 result={'status':'PASS' if not conflicts and not companion_conflicts and not missing else 'CONFLICT','root_hashes':ROOTS,'inputs':{str(p):h for p,h in PINS.items()},'runner_sha256':sha(__file__),'search_path':[str(p) for p in roots],'reader_env':env,'selected_project':selected_objects,'selected_outside':external,'headers':headers,'header_reuse':sorted(reused),'roots':details,'bfs_producer_conflicts':conflicts,'bfs_companion_conflicts':companion_conflicts,'bfs_producer_missing':missing,'batches':batches,'preflight':pre,'postflight':sample(),'scope':'current hypothetical selected project headers and companions; BFS reuse only exact object hashes; outside transitive/dynamic and historical trace75 source-to-object provenance not proved'}
 (O/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':result['status'],'project':len(selected_objects),'outside':len(external),'read_batches':len(batches),'reused':len(reused),'sha256':sha(O/'result.json')}))
 need(result['status']=='PASS','BFS producer mismatch')
except BaseException as e:
 failure={'status':'FAILED','exception':repr(e),'traceback':traceback.format_exc(),'processed':sorted(processed),'unresolved':unresolved,'batches':batches,'time_ns':time.time_ns()}
 (O/'failure.json').write_text(json.dumps(failure,indent=2,sort_keys=True)+'\n');raise
