#!/usr/bin/env python3
"""HELD: rebuild trace75 while preserving the full captured BFS baseline."""
from collections import deque
from hashlib import sha256
from pathlib import Path
import argparse,fcntl,json,os,re,shutil,subprocess,sys,tempfile,time,traceback
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
PLAN=D/'research/trace75-bfs-compatible-provider-plan/observations/plan-attempt01/result.json'
SCAN=D/'research/trace75-bfs-provider-preflight/observations/scan-attempt01/result.json'
BFSATT=D/'research/direct-bfs-80-coherent-rebuild/observations/attempt01'
BFS=BFSATT/'result.json';INITIAL=BFSATT/'initial-project.json';OUTSIDE=BFSATT/'outside-baseline.json'
HELPER=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
UNION=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=LEAN.parent.parent/'lib/lean'
PINS={PLAN:'0a53a6330b8c45fa1830f21b2babc3847f9a46014a33f8db56578a8f9da00088',SCAN:'e27f1cb8694aab43a1023abcce95f7fbc7846d4860dac4b96046391da3dd1e8d',BFS:'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',INITIAL:'a89c775deee5d7f846e85936f2321c1e91d3d5fd51c62b153c2b2dd8e8540f88',OUTSIDE:'5ed42b353836c0cae01a838b701347c7a2c9cc84318e893fbe5c4ae0c7c0b777',HELPER:'886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def rel(n):
 need(re.fullmatch(r'[A-Za-z0-9_\.]+',n) is not None,'bad module '+n);return n.replace('.','/')
def rec(p):
 if not os.path.lexists(p):return None
 need(p.is_file(),'dangling/non-file '+str(p));return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
def bundle(stem):return {s:rec(Path(str(stem)+s)) for s in SUFFIXES}
def hashes(r):return {s:None if r[s] is None else r[s]['sha256'] for s in SUFFIXES}
def check(stem,expected):
 current=bundle(stem);need(hashes(current)==hashes(expected),'companion drift '+str(stem))
 for suffix,old in expected.items():
  if old is not None:need(current[suffix]['resolved']==old['resolved'],'companion target drift '+str(stem)+suffix)
 return current
def resources():
 rows=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in rows if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':live}
def guard():
 x=resources();need(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<2,'resource preflight');return x
def diag(s):return not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',s)
def reports_ok(stdout,stderr,expected_stdout,expected_stderr):
 return stdout==expected_stdout and stderr==expected_stderr and diag(stdout+'\n'+stderr)
def selected(n,roots):
 for root in roots:
  p=root/(rel(n)+'.olean')
  if os.path.lexists(p):need(p.is_file(),'dangling or non-file shadow '+str(p));return p
 return None
def check_copies(copied):
 for p,h in copied.items():
  path=Path(p);need(not path.is_symlink() and path.is_file() and sha(path)==h,'copied source changed '+str(p))
def ensure_vacant(stem):
 for suffix in SUFFIXES:need(not os.path.lexists(Path(str(stem)+suffix)),'refusing clobber '+str(stem)+suffix)

def source_imports(p):return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',p.read_text(),re.M)
def link_bundle(stem,record):
 for suffix,item in record.items():
  dst=Path(str(stem)+suffix)
  if item is None:continue
  need(not os.path.lexists(dst),'refusing clobber '+str(dst));dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(item['path'])
 check(stem,record)
def unlink_bundle(stem):
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):need(p.is_symlink(),'refusing to unlink non-symlink '+str(p));p.unlink()
def monitored(cmd,env,out,err,timeout):
 pre=guard();samples=[];reason=None;start=time.monotonic()
 with out.open('x') as so,err.open('x') as se:
  proc=subprocess.Popen(cmd,env=env,stdout=so,stderr=se)
  try:
   while proc.poll() is None:
    time.sleep(1);s=resources();samples.append(s)
    if s['mem_available_kib']<8*1024**2 or len(s['lean'])>2:reason='resource guard';proc.kill();break
    if time.monotonic()-start>timeout:reason='timeout';proc.kill();break
  finally:
   if proc.poll() is None:proc.kill()
   proc.wait()
 return {'command':cmd,'env':env,'exit':proc.returncode,'reason':reason,'preflight':pre,'postflight':resources(),'samples':samples,'elapsed':time.monotonic()-start,'stdout_sha256':sha(out),'stderr_sha256':sha(err)}
def parse(out,mapping):
 result={};cur=None
 for line in out.splitlines():
  if line.startswith('BEGIN '):need(cur is None and line[6:] in mapping,'bad begin');cur=mapping[line[6:]];need(cur not in result,'duplicate begin');result[cur]=[]
  elif line.startswith('IMPORT ') and cur is not None:result[cur].append(line[7:])
  elif line=='END' and cur is not None:cur=None
  else:raise RuntimeError('malformed header '+line)
 need(cur is None and set(result)==set(mapping.values()),'missing header');return result
parser=argparse.ArgumentParser();parser.add_argument('--preflight-only',action='store_true');parser.add_argument('--attempt');args=parser.parse_args()
need(args.preflight_only != bool(args.attempt),'specify --preflight-only or --attempt')
if args.attempt:need(re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is not None,'bad attempt')
RUNSHA=sha(__file__)
for p,h in PINS.items():need(sha(p)==h,'input pin '+str(p))
plan=json.loads(PLAN.read_text());scan=json.loads(SCAN.read_text());bfs=json.loads(BFS.read_text());initial=json.loads(INITIAL.read_text());outside=json.loads(OUTSIDE.read_text())
need(plan['status']=='PASS' and scan['status']=='PASS' and bfs['status']=='PASS','input status')
order=plan['stage_order'];need(len(order)==31 and len(set(order))==31 and order[-1]=='Trace75FixedCongruence','stage inventory')
prior=bfs['closure']['project'];base=dict(initial);need(not(set(base)&set(bfs['built'])),'base/built collision');base.update(bfs['built']);need(len(base)==1931 and len(outside)==80,'BFS baseline count')
for n in order:
 row=plan['producers'][n];src=Path(row['source']);receipt=Path(row['receipt'])
 need(sha(src)==row['source_sha256'] and sha(receipt)==row['receipt_sha256'],'source/receipt drift '+n)
 att=receipt.parent;historical=json.loads(receipt.read_text())
 need(sha(att/'source.txt')==row['source_sha256'] and sha(att/'stdout')==historical['stdout_sha256'] and sha(att/'stderr')==historical['stderr_sha256'],'producer snapshot/log drift '+n)
 need(source_imports(src)==[i for i in scan['headers'][n] if i!='Init'],'source header mismatch '+n)
 for dep in row['stage_imports']:need(order.index(dep)<order.index(n),'stage topology '+n)
base_now={n:check(UNION/rel(n),record) for n,record in base.items()}
for n,r in base_now.items():
 for s,item in r.items():
  if item is not None:need(item['resolved']==base[n][s]['resolved'],'base target drift '+n+s)
raw=list(UNION.rglob('*.olean'));need(all(p.is_file() for p in raw),'dangling BFS project object')
actual={str(p.relative_to(UNION)) for p in raw}
need(actual=={rel(n)+'.olean' for n in base},'BFS union project inventory changed')
outside_now={}
for n,old in outside.items():
 p=Path(old['.olean']['path']);outside_now[n]=check(Path(str(p)[:-6]),old)
 need(selected(n,[UNION,PACK,CORE])==p,'outside first resolution changed '+n)
classes=plan['classification'];stages=set(order);seeds=set(plan['seeds']);supp={}
for group in ('different','absent'):
 for n,row in classes[group].items():
  if n in stages or n in seeds:continue
  supp[n]=row['trace']
need(len(supp)==15 and len(set(supp)&set(scan['roots']['DirectBFSBandCarry']['project']))==0,'supplement inventory or BFS overlap')
for n,record in supp.items():check(Path(record['.olean']['path'][:-6]),record)
for n in seeds:need(hashes(base_now[n])==hashes(classes['different'][n]['fresh']),'seed not fresh '+n)
pre=guard()
if args.preflight_only:
 print(json.dumps({'status':'PREFLIGHT_PASS','base':len(base),'outside':len(outside),'supplements':len(supp),'stages':len(order),'scanner_sha256':RUNSHA}));raise SystemExit(0)
lock=os.open('/tmp/direct-bfs-80-coherent-rebuild.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600);fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
O=H/'observations'/args.attempt;need(not O.exists(),'attempt exists');O.mkdir(parents=True);root=Path(tempfile.mkdtemp(prefix='trace75-fresh-rebuild-'));lib=root/'lib';srcroot=root/'src';lib.mkdir();srcroot.mkdir()
env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(lib)+':'+str(PACK),'LEAN_NUM_THREADS':'1'};reader_env={'PATH':'/usr/bin:/bin'}
copied={}
result={'status':'FAILED','runner_sha256':RUNSHA,'inputs':{str(p):h for p,h in PINS.items()},'output_root':str(root),'preflight':pre,'stage_order':order,'supplements':sorted(supp),'skipped_existing_supplements':sorted(set(supp)&set(base_now)),'stages':[],'headers':[],'env':env,'reader_env':reader_env,'scope':'capture-relative 31-stage replay preserving the BFS baseline; selected project closure only; outside transitive/dynamic and inherited historical producer ancestry not established'}
def save():
 p=O/'result.tmp';p.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');os.replace(p,O/'result.json')
def stable_sources():
 for n in order:
  row=plan['producers'][n];need(sha(row['source'])==row['source_sha256'] and sha(row['receipt'])==row['receipt_sha256'],'source/receipt changed '+n)
  att=Path(row['receipt']).parent;receipt=json.loads(Path(row['receipt']).read_text())
  need(sha(att/'source.txt')==row['source_sha256'] and sha(att/'stdout')==receipt['stdout_sha256'] and sha(att/'stderr')==receipt['stderr_sha256'],'producer snapshot/log changed '+n)
 check_copies(copied)
 for n,rec0 in supp.items():check(Path(rec0['.olean']['path'][:-6]),rec0)
 for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
 need(sha(__file__)==RUNSHA,'runner changed')
def stable_outside():
 for n,old in outside_now.items():
  p=Path(old['.olean']['path']);need(bundle(Path(str(p)[:-6]))==old,'outside changed '+n)
  need(selected(n,[lib,PACK,CORE])==p,'outside first resolution changed '+n)
def stable_union(expected):
 current={str(p.relative_to(lib)) for p in lib.rglob('*') if p.is_file() or p.is_symlink()}
 for p in lib.rglob('*'):
  if p.is_symlink():need(p.is_file(),'dangling union link '+str(p))
 wanted={rel(n)+suffix for n,old in expected.items() for suffix,item in old.items() if item is not None}
 need(current==wanted,'union inventory changed')
 for n,old in expected.items():check(lib/rel(n),old)
try:
 for n,record in base_now.items():link_bundle(lib/rel(n),record)
 expected=dict(base_now)
 for n,record in supp.items():
  if n in expected:continue
  link_bundle(lib/rel(n),record);expected[n]=record
 for n in order:need(n not in expected,'stage preexists '+n)
 stable_sources();stable_outside();stable_union(expected)
 (O/'initial-union.json').write_text(json.dumps({n:bundle(lib/rel(n)) for n in sorted(expected)},indent=2,sort_keys=True)+'\n')
 result['initial_union_sha256']=sha(O/'initial-union.json');save()
 for i,n in enumerate(order,1):
  row=plan['producers'][n];stage={'index':i,'module':n,'source':row['source'],'source_sha256':row['source_sha256'],'status':'PREPARING'};result['stages'].append(stage);save()
  stable_sources();stable_outside();stable_union(expected)
  for dep in row['stage_imports']:need(dep in expected,'stage dependency absent '+n+' '+dep)
  source=srcroot/(n+'.lean');shutil.copyfile(row['source'],source);need(sha(source)==row['source_sha256'],'copied source drift '+n)
  snapshot=O/(f'stage-{i:02}.source.lean');shutil.copyfile(source,snapshot);copied[str(source)]=row['source_sha256'];copied[str(snapshot)]=row['source_sha256'];check_copies(copied)
  output=lib/(rel(n)+'.olean');ensure_vacant(lib/rel(n))
  cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={srcroot}',str(source),'-o',str(output)]
  stage.update({'status':'RUNNING','command':cmd});save()
  run=monitored(cmd,env,O/(f'stage-{i:02}.stdout'),O/(f'stage-{i:02}.stderr'),600);stage.update(run);stage['status']='CHECKING';save()
  att=Path(row['receipt']).parent;expected_stdout=(att/'stdout').read_text();expected_stderr=(att/'stderr').read_text()
  need(run['exit']==0 and run['reason'] is None and output.is_file() and reports_ok((O/(f'stage-{i:02}.stdout')).read_text(),(O/(f'stage-{i:02}.stderr')).read_text(),expected_stdout,expected_stderr),'stage failed '+n)
  check_copies(copied);need(not output.is_symlink(),'stage output is symlink '+n);expected[n]=bundle(lib/rel(n));stage['object']=expected[n];stage['status']='PASS'
  stable_sources();stable_outside();stable_union(expected);save()
 # Actual post-build serialized closure for the trace endpoint and the captured BFS carry provider.
 roots=['Trace75FixedCongruence','DirectBFSBandCarry','DirectBFSHaltPellSeed'];todo=deque(roots);seen=set();objects={};ext={};heads={};reused=[]
 while todo:
  batch=[]
  while todo and len(batch)<32:
   n=todo.popleft()
   if n in seen:continue
   seen.add(n);path=lib/(rel(n)+'.olean')
   found=selected(n,[lib,PACK,CORE]);need(found is not None,'unresolved module '+n)
   if found!=path:
    ext[n]=bundle(Path(str(found)[:-6]));continue
   objects[n]=bundle(lib/rel(n));h=objects[n]['.olean']['sha256'];cached=scan['selected_project'].get(n);old=prior.get(n)
   if cached is not None and cached['.olean']['sha256']==h:heads[n]=scan['headers'][n];reused.append(n);todo.extend(heads[n])
   elif old is not None and old['record']['sha256']==h:heads[n]=old['imports'];reused.append(n);todo.extend(heads[n])
   else:batch.append((n,path))
  if not batch:continue
  i=len(result['headers']);out=O/(f'header-{i:03}.stdout');err=O/(f'header-{i:03}.stderr');cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER)]+[str(p) for _,p in batch]
  result['headers'].append({'status':'RUNNING','command':cmd});save();run=monitored(cmd,reader_env,out,err,45);result['headers'][-1].update(run);save()
  need(run['exit']==0 and run['reason'] is None and not err.read_text(),'header read failed');new=parse(out.read_text(),{str(p):n for n,p in batch});heads.update(new)
  for v in new.values():todo.extend(v)
  result['headers'][-1]['status']='PASS';save()
 def closure(r):
  q=[r];inside=set();outside_names=set()
  while q:
   n=q.pop()
   if n in inside or n in outside_names:continue
   if n not in heads:outside_names.add(n);continue
   inside.add(n);q.extend(heads[n])
  return inside,outside_names
 summaries={}
 for r in roots:
  inside,out=closure(r);need(out<=set(ext),'closure boundary missing '+r);summaries[r]={'project':sorted(inside),'outside':sorted(out)}
 for rootname in ('DirectBFSBandCarry','DirectBFSHaltPellSeed'):
  for n in summaries[rootname]['project']:
   need(n in prior,'missing BFS capture '+n)
   need(hashes(objects[n])==hashes(prior[n]['companions']),'BFS selected companion mismatch '+n)
 for n in order:need(heads[n]==scan['headers'][n],'rebuilt source header changed '+n)
 for n in seeds:need(objects[n]['.olean']['sha256']==base_now[n]['.olean']['sha256'],'fresh seed not selected '+n)
 for n,r in ext.items():need(n in outside and hashes(r)==hashes(outside[n]),'outside capture mismatch '+n)
 stable_sources();stable_outside();stable_union(expected)
 result.update({'status':'PASS','selected_project':objects,'selected_outside':ext,'serialized_headers':heads,'header_reuse':sorted(reused),'closures':summaries,'union_count':len(expected),'postflight':resources()});save()
 print(json.dumps({'status':'PASS','root':str(root),'stages':len(order),'project':len(objects),'outside':len(ext),'result_sha256':sha(O/'result.json')}))
except BaseException as e:
 result.update({'status':'FAILED','exception':repr(e),'traceback':traceback.format_exc(),'postflight':resources()});save();raise
