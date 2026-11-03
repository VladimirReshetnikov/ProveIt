#!/usr/bin/env python3
"""Parent-pinned preflight/assembly; independent review required before Lean."""
from collections import deque
from hashlib import sha256
from pathlib import Path
import argparse,fcntl,json,os,re,shutil,subprocess,sys,tempfile,time,traceback
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
PARENT_DIR=D/'research/trace75-bfs-compatible-forward-rebuild/observations/attempt01'
PARENT=PARENT_DIR/'result.json';PARENT_OUTER=D/'research/trace75-bfs-compatible-forward-rebuild/observations/outer-attempt01/terminal.json'
# Set these only from a terminal PASS parent and a separately captured actual outer exit.
PARENT_SHA='f8d6388911e101a7dfae2547907bc6f9245950fa953c3a4769eff00c140fc3d8';PARENT_OUTER_SHA='5b286234c26c06db503ff6a485aeac2a9e57afc76205c189a30bb8e07e7316c5'
SPLAN=H/'plan.json'
FORWARD_PLAN=D/'research/trace75-bfs-compatible-forward-plan/observations/plan-attempt01/result.json'
CANON=D/'Lean/DiophantineConsistency/TenPositiveTrace75Syntax.lean'
EXTRA=D/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
BFS_DIR=D/'research/direct-bfs-80-coherent-rebuild/observations/attempt01'
BFS=BFS_DIR/'result.json';INITIAL=BFS_DIR/'initial-project.json';OUTSIDE=BFS_DIR/'outside-baseline.json'
CPLAN=D/'research/trace75-bfs-compatible-provider-plan/observations/plan-attempt01/result.json'
RPLAN=D/'research/trace75-bfs-compatible-reverse-plan/observations/source-plan-attempt01/result.json'
HELPER=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
BASE=Path('/tmp/trace75-compatible-forward-dbe4ma6p/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=LEAN.parent.parent/'lib/lean'
PINS={RPLAN:'369d06ba5bd50b038d7279324819bcb76bb45e7bc8c0c1ff727eccb3c32c86af',SPLAN:'04559737ca02dc639ea0ac3a24bfd72997a9bae1f38c6d42b4da944b6a751dd6',FORWARD_PLAN:'baa12a3a2a04ecfa32e0f925c8a79a4b2f7b520691a6c506a851b6f7a3473199',CANON:'6c18ae1ceff5815d4093e6f014fbeaed4ba8de45a1624d88cc9a3ee54306487f',EXTRA:'8847a09fb7925816ab7ceaab0d61a12c0b814b2a7571daae32ea1f510c779016',BFS:'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',INITIAL:'a89c775deee5d7f846e85936f2321c1e91d3d5fd51c62b153c2b2dd8e8540f88',OUTSIDE:'5ed42b353836c0cae01a838b701347c7a2c9cc84318e893fbe5c4ae0c7c0b777',CPLAN:'0a53a6330b8c45fa1830f21b2babc3847f9a46014a33f8db56578a8f9da00088',HELPER:'886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
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

def header_matches(actual,imports):return 'Init' in actual and [x for x in actual if x!='Init']==imports
def direct_bundle_matches(selected,reference):return hashes(selected)==hashes(reference)
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
def stage_reports_ok(module,stdout,stderr):
 if stderr or not diag(stdout):return False
 expected={
  'DiophantineConsistency.TenPositiveTrace75Syntax':['DiophantineConsistency.TenPositiveTrace75.evalRing_expression'],
  'Trace75BFSSyntax':['Trace75BFSSyntax.literal_zero_iff'],
  'Trace75BFSModelIff':['Trace75BFSModelIff.positive_model_iff'],
  'Trace75BFSIPRA':['Trace75BFSIPRA.'+x for x in ['positive_bridge','native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']],
  'Trace75BFSFixedIPRA':['Trace75BFSFixedIPRA.'+x for x in ['native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']]}
 pattern=r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
 found=re.findall(pattern,stdout,re.S)
 if re.sub(pattern,'',stdout,flags=re.S).strip():return False
 allowed={'propext','Classical.choice','Quot.sound'}
 return [n for n,_ in found]==expected[module] and all(set(x.strip() for x in ax.split(',') if x.strip())<=allowed for _,ax in found)
parser=argparse.ArgumentParser();parser.add_argument('--preflight-only',action='store_true');parser.add_argument('--attempt');args=parser.parse_args()
need(args.preflight_only != bool(args.attempt),'specify --preflight-only or --attempt')
if args.attempt:need(re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is not None,'bad attempt')
need(re.fullmatch(r'[0-9a-f]{64}',PARENT_SHA) is not None and re.fullmatch(r'[0-9a-f]{64}',PARENT_OUTER_SHA) is not None,'parent result and outer must be pinned after terminal')
PINS.update({PARENT:PARENT_SHA,PARENT_OUTER:PARENT_OUTER_SHA});RUNSHA=sha(__file__)
for p,h in PINS.items():need(sha(p)==h,'input pin '+str(p))
parent=json.loads(PARENT.read_text());outer=json.loads(PARENT_OUTER.read_text());plan=json.loads(SPLAN.read_text());rplan=json.loads(RPLAN.read_text());extra=json.loads(EXTRA.read_text());bfs=json.loads(BFS.read_text());initial=json.loads(INITIAL.read_text());outside=json.loads(OUTSIDE.read_text());cplan=json.loads(CPLAN.read_text())
need(parent['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==PARENT_SHA,'parent terminal status or outer receipt')
need(Path(parent['output_root'])/'lib'==BASE and len(parent['stages'])==21 and all(s['status']=='PASS' for s in parent['stages']),'parent output or stage status')
parent_order=[s['module'] for s in parent['stages']];need(parent_order==[r['module'] for r in json.loads(FORWARD_PLAN.read_text())['stages']] and len(set(parent_order))==21,'parent stage sequence changed')
need(outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after'],'parent outer input drift')
need(plan['status']=='HELD_AWAITING_FORWARD_RESULT_AND_OUTER_EXIT' and extra['status']=='PASS' and bfs['status']=='PASS' and cplan['status']=='PASS','plan or BFS status')
parent_initial=PARENT_DIR/'initial-union.json';need(sha(parent_initial)==parent['initial_union_sha256'],'parent initial union changed');PINS[parent_initial]=parent['initial_union_sha256']
base=json.loads(parent_initial.read_text())
for s in parent['stages']:
 n=s['module'];need(n not in base,'parent stage collision '+n);base[n]=s['object']
need(len(base)==parent['union_count'],'parent union count')
prior=bfs['closure']['project'];oldbase=dict(initial);need(not (set(oldbase)&set(bfs['built'])),'BFS baseline collision');oldbase.update(bfs['built'])
for n in oldbase:need(n in base and hashes(base[n])==hashes(oldbase[n]),'BFS object changed '+n)
inherited=cplan['inherited_baseline_affected'];need(len(inherited)==4 and len(set(inherited))==4,'inherited four inventory')
for n in inherited:need(n in oldbase and hashes(base[n])==hashes(oldbase[n]),'inherited baseline object changed '+n)
need(extra['module'] not in outside,'extra outside shadows BFS outside');outside[extra['module']]=extra['record']
need(len(outside)==81,'outside baseline count changed')
rows=plan['stages'];order=[r['module'] for r in rows]
need(len(order)==5 and len(set(order))==5 and order[-1]=='Trace75BFSFixedIPRA','assembly stage inventory')
for i,r in enumerate(rows):
 n=r['module'];r['source']=str(D/r['source']);r['source_sha256']=r['sha256']
 need(n not in base,'assembly stage already in parent '+n)
 need(sha(r['source'])==r['source_sha256'],'source drift '+n)
 need(source_imports(Path(r['source']))==r['imports'],'source direct import drift '+n)
 r['direct']={}
 for dep in r['imports']:
  if dep in order:
   need(order.index(dep)<i,'assembly topology '+n+' '+dep);r['direct'][dep]={'kind':'stage'}
  else:
   need(dep in base,'missing parent direct project import '+n+' '+dep);r['direct'][dep]={'kind':'project'}
need(Path(rows[0]['source']).read_bytes()==CANON.read_bytes()+b'\n#print axioms DiophantineConsistency.TenPositiveTrace75.evalRing_expression\n','syntax instrumentation mismatch')
base_now={n:check(BASE/rel(n),record) for n,record in base.items()}
actual={str(p.relative_to(BASE)) for p in BASE.rglob('*') if p.is_file() or p.is_symlink()};wanted={rel(n)+s for n,r in base.items() for s,v in r.items() if v is not None};need(actual==wanted,'parent full union inventory drift')
outside_now={}
for n,record in outside.items():
 p=Path(record['.olean']['path']);outside_now[n]=check(Path(str(p)[:-6]),record);need(selected(n,[BASE,PACK,CORE])==p,'parent outside first resolution changed '+n)
for r in rows:
 for dep,ref in r['direct'].items():
  if ref['kind']=='stage':continue
  p=selected(dep,[BASE,PACK,CORE]);want=base_now[dep]['.olean'] if ref['kind']=='project' else outside_now[dep]['.olean'];need(p is not None and sha(p)==want['sha256'] and str(p.resolve(strict=True))==want['resolved'],'direct input mismatch '+dep)
  selected_bundle=base_now[dep] if ref['kind']=='project' else outside_now[dep]
  need(hashes(bundle(Path(str(p)[:-6])))==hashes(selected_bundle),'direct companion drift '+dep)
need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
pre=guard()
if args.preflight_only:
 print(json.dumps({'status':'PREFLIGHT_PASS','parent':len(base),'outside':len(outside),'stages':len(order),'inherited_four':inherited,'runner_sha256':RUNSHA}));raise SystemExit(0)
lock=os.open('/tmp/direct-bfs-80-coherent-rebuild.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600);fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
O=H/'observations'/args.attempt;need(not os.path.lexists(O),'attempt exists');O.mkdir(parents=True);root=Path(tempfile.mkdtemp(prefix='trace75-final-assembly-'));lib=root/'lib';srcroot=root/'src';lib.mkdir();srcroot.mkdir()
env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(lib)+':'+str(PACK),'LEAN_NUM_THREADS':'1'};reader_env={'PATH':'/usr/bin:/bin'};copied={}
result={'status':'FAILED','runner_sha256':RUNSHA,'inputs':{str(p):h for p,h in PINS.items()},'output_root':str(root),'preflight':pre,'stage_order':order,'stages':[],'headers':[],'inherited_baseline_four':inherited,'scope':'HELD final trace75 assembly on compatible parent; four retained baseline nodes, inherited project/outside/package/dynamic ancestry and external equation-file binding remain unproved'}
def save():
 p=O/'result.tmp';p.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');os.replace(p,O/'result.json')
def stable_inputs():
 for p,h in PINS.items():need(sha(p)==h,'pinned input changed '+str(p))
 need(sha(__file__)==RUNSHA,'runner changed')
 for r in rows:
  need(sha(r['source'])==r['source_sha256'],'stage source changed '+r['module'])
 check_copies(copied)
def stable_base():
 current={str(p.relative_to(BASE)) for p in BASE.rglob('*') if p.is_file() or p.is_symlink()};need(current==wanted,'parent inventory changed')
 for n,old in base.items():check(BASE/rel(n),old)
def stable_outside():
 for n,old in outside_now.items():
  p=Path(old['.olean']['path']);need(bundle(Path(str(p)[:-6]))==old,'outside bundle changed '+n);need(selected(n,[lib,PACK,CORE])==p,'outside first resolution changed '+n)
def stable_union(expected):
 current={str(p.relative_to(lib)) for p in lib.rglob('*') if p.is_file() or p.is_symlink()}
 for p in lib.rglob('*'):
  if p.is_symlink():need(p.is_file(),'dangling union link '+str(p))
 want={rel(n)+s for n,r in expected.items() for s,v in r.items() if v is not None};need(current==want,'new union inventory changed')
 for n,old in expected.items():check(lib/rel(n),old)
try:
 for n,record in base_now.items():link_bundle(lib/rel(n),record)
 expected=dict(base_now);stable_inputs();stable_base();stable_outside();stable_union(expected)
 (O/'initial-union.json').write_text(json.dumps({n:bundle(lib/rel(n)) for n in sorted(expected)},indent=2,sort_keys=True)+'\n');result['initial_union_sha256']=sha(O/'initial-union.json');save()
 for i,r in enumerate(rows,1):
  n=r['module'];stage={'index':i,'module':n,'source':r['source'],'source_sha256':r['source_sha256'],'status':'PREPARING'};result['stages'].append(stage);save()
  stable_inputs();stable_base();stable_outside();stable_union(expected)
  direct_before={}
  for dep,ref in r['direct'].items():
   p=selected(dep,[lib,PACK,CORE]);need(p is not None,'unresolved direct '+dep)
   old=expected.get(dep) if ref['kind']!='outside' else outside_now.get(dep);need(old is not None and sha(p)==old['.olean']['sha256'] and str(p.resolve(strict=True))==old['.olean']['resolved'],'direct selection drift '+dep)
   current=bundle(Path(str(p)[:-6]));need(hashes(current)==hashes(old),'direct companion drift '+dep);direct_before[dep]=current
  stage['direct_imports']=direct_before
  source=srcroot/(rel(n)+'.lean');source.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(r['source'],source);snapshot=O/(f'stage-{i:02}.source.lean');shutil.copyfile(source,snapshot);copied[str(source)]=r['source_sha256'];copied[str(snapshot)]=r['source_sha256'];check_copies(copied)
  output=lib/(rel(n)+'.olean');ensure_vacant(lib/rel(n));cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={srcroot}',str(source),'-o',str(output)]
  stage.update({'status':'RUNNING','command':cmd});save();run=monitored(cmd,env,O/(f'stage-{i:02}.stdout'),O/(f'stage-{i:02}.stderr'),600);stage.update(run);stage['status']='CHECKING';save()
  need(run['exit']==0 and run['reason'] is None and output.is_file() and not output.is_symlink() and stage_reports_ok(n,(O/(f'stage-{i:02}.stdout')).read_text(),(O/(f'stage-{i:02}.stderr')).read_text()),'stage failed '+n)
  direct_after={}
  for dep,old in direct_before.items():
   p=selected(dep,[lib,PACK,CORE]);need(p is not None,'direct import vanished '+dep)
   current=bundle(Path(str(p)[:-6]));need(current==old,'direct import changed '+dep);direct_after[dep]=current
  stage['direct_imports_after']=direct_after
  check_copies(copied);expected[n]=bundle(lib/rel(n));stage['object']=expected[n];stage['status']='PASS';stable_inputs();stable_base();stable_outside();stable_union(expected);save()
 # Reconstruct selected headers for reverse output and the same two captured BFS roots.
 roots=['Trace75BFSFixedIPRA','Trace75BFSModelHalt','Trace75BFSHaltGraph','DirectBFSBandCarry','DirectBFSHaltPellSeed'];todo=deque(roots);seen=set();objects={};ext={};heads={};reused=[]
 while todo:
  batch=[]
  while todo and len(batch)<32:
   n=todo.popleft()
   if n in seen:continue
   seen.add(n);path=lib/(rel(n)+'.olean');found=selected(n,[lib,PACK,CORE]);need(found is not None,'unresolved closure module '+n)
   if found!=path:ext[n]=bundle(Path(str(found)[:-6]));continue
   objects[n]=bundle(lib/rel(n));h=objects[n]['.olean']['sha256'];cached=parent['selected_project'].get(n);old=prior.get(n)
   if cached is not None and cached['.olean']['sha256']==h:heads[n]=parent['serialized_headers'][n];reused.append(n);todo.extend(heads[n])
   elif old is not None and old['record']['sha256']==h:heads[n]=old['imports'];reused.append(n);todo.extend(heads[n])
   else:batch.append((n,path))
  if not batch:continue
  i=len(result['headers']);out=O/(f'header-{i:03}.stdout');err=O/(f'header-{i:03}.stderr');cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER)]+[str(p) for _,p in batch]
  result['headers'].append({'status':'RUNNING','command':cmd});save();run=monitored(cmd,reader_env,out,err,60);result['headers'][-1].update(run);save();need(run['exit']==0 and run['reason'] is None and not err.read_text(),'header read failed')
  new=parse(out.read_text(),{str(p):n for n,p in batch});heads.update(new)
  for v in new.values():todo.extend(v)
  result['headers'][-1]['status']='PASS';save()
 def closure(r):
  todo=[r];inside=set();out=set()
  while todo:
   n=todo.pop()
   if n in inside or n in out:continue
   if n not in heads:out.add(n);continue
   inside.add(n);todo.extend(heads[n])
  return inside,out
 summaries={}
 for n in roots:
  ins,out=closure(n);need(out<=set(ext),'outside closure missing '+n);summaries[n]={'project':sorted(ins),'outside':sorted(out)}
 for n in ('DirectBFSBandCarry','DirectBFSHaltPellSeed'):
  need(summaries[n]==parent['closures'][n],'BFS closure set changed '+n)
  for dep in summaries[n]['project']:need(dep in prior and hashes(objects[dep])==hashes(prior[dep]['companions']),'BFS closure companion changed '+dep)
 for rootname in ('Trace75BFSHaltGraph','Trace75BFSModelHalt'):
  need(summaries[rootname]==parent['closures'][rootname],'parent closure set changed '+rootname)
  for dep in summaries[rootname]['project']:need(dep in parent['selected_project'] and hashes(objects[dep])==hashes(parent['selected_project'][dep]),'parent closure companion changed '+dep)
  for dep in summaries[rootname]['outside']:need(dep in parent['selected_outside'] and hashes(ext[dep])==hashes(parent['selected_outside'][dep]),'parent outside companion changed '+dep)
 for r in rows:
  actual_imports=heads[r['module']];need(header_matches(actual_imports,r['imports']),'assembly serialized source imports changed '+r['module'])
 for n,rec0 in ext.items():need(n in outside_now and hashes(rec0)==hashes(outside_now[n]),'unrecorded outside closure '+n)
 stable_inputs();stable_base();stable_outside();stable_union(expected)
 result.update({'status':'PASS','selected_project':objects,'selected_outside':ext,'serialized_headers':heads,'header_reuse':sorted(reused),'closures':summaries,'union_count':len(expected),'postflight':resources()});save()
 print(json.dumps({'status':'PASS','root':str(root),'stages':len(order),'result_sha256':sha(O/'result.json')}))
except BaseException as e:
 result.update({'status':'FAILED','exception':repr(e),'traceback':traceback.format_exc(),'postflight':resources()});save();raise
