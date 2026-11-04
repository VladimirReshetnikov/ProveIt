#!/usr/bin/env python3
"""HELD: reverse parent pinned; independent review required before any Lean invocation."""
from collections import deque
from hashlib import sha256
from pathlib import Path
import argparse,fcntl,json,os,re,shutil,subprocess,sys,tempfile,time,traceback
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
PARENT_DIR=D/'research/trace74-conditional-saturation-guard-rebuild/observations/attempt02'
PARENT=PARENT_DIR/'result.json';PARENT_OUTER=D/'research/trace74-conditional-saturation-guard-rebuild/observations/outer-attempt02/terminal.json'
# Set these only from a terminal PASS parent and a separately captured actual outer exit.
PARENT_SHA='a55113d40aeae95bc420b51d1a1a2809a3ed4bb28968af45b22b4152e6501709';PARENT_OUTER_SHA='b8108201952a11db44245fec9d671ddbbf6897a78726ba10aaf94254d541997a'
SPLAN=H/'source-plan.json'
EXTRA=D/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
BFS_DIR=D/'research/direct-bfs-80-coherent-rebuild/observations/attempt01'
BFS=BFS_DIR/'result.json';INITIAL=BFS_DIR/'initial-project.json';OUTSIDE=BFS_DIR/'outside-baseline.json'
CPLAN=D/'research/trace75-bfs-compatible-provider-plan/observations/plan-attempt01/result.json'
RPLAN=D/'research/trace75-bfs-compatible-reverse-plan/observations/source-plan-attempt01/result.json'
HELPER=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
BASE=Path('/tmp/trace74-conditional-saturation-guard-c4x4yq_y/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=LEAN.parent.parent/'lib/lean'
PINS={RPLAN:'369d06ba5bd50b038d7279324819bcb76bb45e7bc8c0c1ff727eccb3c32c86af',SPLAN:'4e6cd32c32d20ed403f27ed5dc61f4453781c6567630f64842463e8ce6c8bd98',EXTRA:'8847a09fb7925816ab7ceaab0d61a12c0b814b2a7571daae32ea1f510c779016',BFS:'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',INITIAL:'a89c775deee5d7f846e85936f2321c1e91d3d5fd51c62b153c2b2dd8e8540f88',OUTSIDE:'5ed42b353836c0cae01a838b701347c7a2c9cc84318e893fbe5c4ae0c7c0b777',CPLAN:'0a53a6330b8c45fa1830f21b2babc3847f9a46014a33f8db56578a8f9da00088',HELPER:'886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
ASSEMBLY_AUDIT=D/'reviews/trace75-bfs-final-assembly-result-independent/README.md'
MASK_OBS=D/'research/trace75-mask-coordinate-ring-probe/observations/ring-attempt02'
PINS.update({ASSEMBLY_AUDIT:'d99de3ef2a5bd0b08af624e2421f4cc10f6eb9a9886eb67a94016a237d6b2c6b',MASK_OBS/'terminal.json':'4be85ee6a9e08695c3f67e1d1154108cdb601308ac4c1da46b6f4a24e9559fc9',MASK_OBS/'source.txt':'83ad7a62d50b10104099d8769c201c5514ed3afdabcf30ce1df8f4bb7774b7f0',MASK_OBS/'stdout':'916d40ebaa640125ae59cb04c032c54e7b9ddf81abbc74b8773e5a2a36e7e355',MASK_OBS/'stderr':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'})
BOUNDARY_AUDIT=D/'reviews/trace74-boundary-compatible-result-independent/README.md'
DRAFT_AUDIT=D/'reviews/trace74-boundary-witness-draft-independent/README.md'
PINS.update({BOUNDARY_AUDIT:'cfce71fa601910a41c86106b8421ddff024d906a711ae02ab5de3c61abc2e14b',DRAFT_AUDIT:'e7b221e58721eefc36f537b84dc1fc5fc9d28ce71df02bee725285682df2a66e'})
WITNESS_AUDIT=D/'reviews/trace74-boundary-witness-result-independent/README.md'
PARAMETRIC_AUDIT=D/'reviews/trace74-symbolic-beta-power-failure-v2-draft-independent/README.md'
PINS.update({WITNESS_AUDIT:'33fc5d7e79463eda0b587a77ade9590f663cacc8519b9eda9d7f15c5f578337c',PARAMETRIC_AUDIT:'aa76151edc1a190f5a0d44647619a96d3b2fa5333f9f6dd694fbb9e347e9d804'})
PINS[D/'reviews/trace74-boundary-seed-parametric-result-independent/README.md']='90c76e3061cb386e1eb5fb10d8f575f205c0e934f2c781da97584f65fd9ddbce'
PINS[D/'reviews/trace74-boundary-natural-seed-result-independent/README.md']='ddd6ace8f0d78fcd512d4dbd49534a7feca1277bda03666d9e88b278d3c515e9'
PINS[D/'reviews/trace74-boundary-generic-cast-transfer-result-independent/README.md']='9a20b57ca6b3f77cae0f1c945288cffbda033a06a97106477787b09f9dae87a5'
PINS[D/'reviews/trace74-boundary-generic-assembly-result-independent/README.md']='0800e9b5d157660c46d7c3997958d255d38cfd3d3dcc98ef701eee2daca71e5d'
PINS[D/'reviews/trace74-boundary-seed-specialization-result-independent/README.md']='f6d8d0ac136014b81e31310f683521b1cd7fe20ba1dfd79a2b03981a635869ba'
PINS[D/'reviews/trace74-boundary-seed-model-facts-result-independent/README.md']='fde0dff0ef1ad05118663b5c99bc375ff232ff43e3cef4f48e51452d643a7b8e'
PINS[D/'reviews/trace74-direct-four-block-result-independent/README.md']='472424fa3c7b86b96143be91e9b94695f41199bd55368cf36fe3cb5be571cb1d'
PINS[D/'reviews/trace74-conditional-saturation-guard-result-independent/README.md']='7cb3bae10c2b9219b6aced1eb5c2e3fd621f979eb29b5f33a8ac02a98821d99a'
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
def reports_ok(stdout,stderr,names):
 if stderr or not diag(stdout+'\n'+stderr):return False
 pattern=re.compile(r"'([^'\n]+)' (?:does not depend on any axioms|depends on axioms: \[([A-Za-z0-9_., \n]*)\])\n")
 allowed={'propext','Classical.choice','Quot.sound'};pos=0;seen=[]
 while pos<len(stdout):
  m=pattern.match(stdout,pos)
  if not m:return False
  seen.append(m.group(1));raw=m.group(2)
  if raw is not None:
   atoms=[x.strip() for x in raw.split(',')] if raw.strip() else []
   if not all(atoms) or len(atoms)!=len(set(atoms)) or not set(atoms)<=allowed:return False
  pos=m.end()
 return seen==names and len(set(names))==len(names)
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
parser=argparse.ArgumentParser();parser.add_argument('--preflight-only',action='store_true');parser.add_argument('--attempt');args=parser.parse_args()
need(args.preflight_only != bool(args.attempt),'specify --preflight-only or --attempt')
if args.attempt:need(re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is not None,'bad attempt')
need(re.fullmatch(r'[0-9a-f]{64}',PARENT_SHA) is not None and re.fullmatch(r'[0-9a-f]{64}',PARENT_OUTER_SHA) is not None,'parent result and outer must be pinned after terminal')
PINS.update({PARENT:PARENT_SHA,PARENT_OUTER:PARENT_OUTER_SHA});RUNSHA=sha(__file__)
for p,h in PINS.items():need(sha(p)==h,'input pin '+str(p))
parent=json.loads(PARENT.read_text());outer=json.loads(PARENT_OUTER.read_text());plan=json.loads(SPLAN.read_text());rplan=json.loads(RPLAN.read_text());extra=json.loads(EXTRA.read_text());bfs=json.loads(BFS.read_text());initial=json.loads(INITIAL.read_text());outside=json.loads(OUTSIDE.read_text());cplan=json.loads(CPLAN.read_text())
need(parent['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==PARENT_SHA,'parent terminal status or outer receipt')
need(Path(parent['output_root'])/'lib'==BASE and len(parent['stages'])==1 and all(s['status']=='PASS' for s in parent['stages']),'parent output or stage status')
parent_order=[s['module'] for s in parent['stages']];need(parent_order==['Trace74ConditionalSaturationGuard'] and len(set(parent_order))==1,'parent stage sequence changed')
need(outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after'],'parent outer input drift')
need(plan['status']=='PASS' and extra['status']=='PASS' and bfs['status']=='PASS' and cplan['status']=='PASS','plan or BFS status')
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
rows=plan['stages'];order=[r['module'] for r in rows];need(len(order)==1 and len(set(order))==1 and order[-1]=='Trace74BetaPower','reverse stage inventory')
for r in rows:
 n=r['module'];need(n not in base,'reverse stage already in parent '+n)
 need(sha(r['source'])==r['source_sha256'],'draft source drift '+n)
 need(source_imports(Path(r['source']))==r['imports'],'source direct import drift '+n)
 for dep,ref in r['direct'].items():
  if ref['kind']=='stage':need(dep in order and order.index(dep)<order.index(n),'reverse topology '+n+' '+dep)
  elif ref['kind']=='project':need(dep in base,'missing parent direct project import '+n+' '+dep)
  else:need(dep in outside,'unrecorded direct outside import '+n+' '+dep)
base_now={n:check(BASE/rel(n),record) for n,record in base.items()}
actual={str(p.relative_to(BASE)) for p in BASE.rglob('*') if p.is_file() or p.is_symlink()};wanted={rel(n)+s for n,r in base.items() for s,v in r.items() if v is not None};need(actual==wanted,'parent full union inventory drift')
outside_now={}
for n,record in outside.items():
 p=Path(record['.olean']['path']);outside_now[n]=check(Path(str(p)[:-6]),record);need(selected(n,[BASE,PACK,CORE])==p,'parent outside first resolution changed '+n)
for r in rows:
 for dep,ref in r['direct'].items():
  if ref['kind']=='stage':continue
  p=selected(dep,[BASE,PACK,CORE]);want=base_now[dep]['.olean'] if ref['kind']=='project' else outside_now[dep]['.olean'];need(p is not None and sha(p)==want['sha256'] and str(p.resolve(strict=True))==want['resolved'],'direct input mismatch '+dep)
  need(sha(p)==ref['sha256'] and str(p.resolve(strict=True))==ref['resolved'],'planned direct input drift '+dep)
need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
pre=guard()
if args.preflight_only:
 print(json.dumps({'status':'PREFLIGHT_PASS','parent':len(base),'outside':len(outside),'stages':len(order),'inherited_four':inherited,'runner_sha256':RUNSHA}));raise SystemExit(0)
lock=os.open('/tmp/direct-bfs-80-coherent-rebuild.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600);fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
O=H/'observations'/args.attempt;need(not os.path.lexists(O),'attempt exists');O.mkdir(parents=True);root=Path(tempfile.mkdtemp(prefix='trace74-symbolic-fixed-mask-cover-'));lib=root/'lib';srcroot=root/'src';lib.mkdir();srcroot.mkdir()
env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(lib)+':'+str(PACK),'LEAN_NUM_THREADS':'1'};reader_env={'PATH':'/usr/bin:/bin'};copied={}
result={'status':'FAILED','runner_sha256':RUNSHA,'inputs':{str(p):h for p,h in PINS.items()},'output_root':str(root),'preflight':pre,'stage_order':order,'stages':[],'headers':[],'inherited_baseline_four':inherited,'scope':'capture-relative one-stage symbolic fixed-mask cover draft check; four retained nodes source ancestry, transitive outside/package/dynamic ancestry and external equation-file binding remain unproved; no concrete 74 zero, fixed-port conclusion, or iPRA endpoint'}
def save():
 p=O/'result.tmp';p.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');os.replace(p,O/'result.json')
def stable_inputs():
 for p,h in PINS.items():need(sha(p)==h,'pinned input changed '+str(p))
 need(sha(__file__)==RUNSHA,'runner changed')
 for r in rows:
  need(sha(r['source'])==r['source_sha256'],'draft source changed '+r['module'])
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
  for dep,ref in r['direct'].items():
   p=selected(dep,[lib,PACK,CORE]);need(p is not None,'unresolved direct '+dep)
   old=expected.get(dep) if ref['kind']!='outside' else outside_now.get(dep);need(old is not None and sha(p)==old['.olean']['sha256'] and str(p.resolve(strict=True))==old['.olean']['resolved'],'direct selection drift '+dep)
  source=srcroot/(n+'.lean');shutil.copyfile(r['source'],source);snapshot=O/(f'stage-{i:02}.source.lean');shutil.copyfile(source,snapshot);copied[str(source)]=r['source_sha256'];copied[str(snapshot)]=r['source_sha256'];check_copies(copied)
  output=lib/(rel(n)+'.olean');ensure_vacant(lib/rel(n));cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={srcroot}',str(source),'-o',str(output)]
  stage.update({'status':'RUNNING','command':cmd});save();run=monitored(cmd,env,O/(f'stage-{i:02}.stdout'),O/(f'stage-{i:02}.stderr'),600);stage.update(run);stage['status']='CHECKING';save()
  report_names=r['reports']
  need(report_names==['Trace74BetaPower.beta_plus_one'],'unexpected report inventory')
  need(run['exit']==0 and run['reason'] is None and output.is_file() and not output.is_symlink() and reports_ok((O/(f'stage-{i:02}.stdout')).read_text(),(O/(f'stage-{i:02}.stderr')).read_text(),report_names),'stage failed '+n)
  check_copies(copied);expected[n]=bundle(lib/rel(n));stage['object']=expected[n];stage['status']='PASS';stable_inputs();stable_base();stable_outside();stable_union(expected);save()
 # Reconstruct selected headers for reverse output and the same two captured BFS roots.
 roots=['Trace74BetaPower','Trace74ConditionalSaturationGuard','Trace74DirectFourBlock','Trace74BoundaryConcreteZero','Trace74BoundarySeedModelFacts','Trace74BoundarySeedSpecialization','Trace74BoundaryGenericAssembly','Trace74BoundaryGenericCastTransfer','Trace74BoundaryNaturalSeed','Trace74BoundaryRecurrenceCast','Trace74BoundarySeedParametric','Trace74BoundaryGraphWitness','Trace74BoundaryGraph','Trace75BFSFixedIPRA','Trace75BFSModelHalt','Trace75BFSHaltGraph','DirectBFSBandCarry','DirectBFSHaltPellSeed'];todo=deque(roots);seen=set();objects={};ext={};heads={};reused=[]
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
 for saved in ('Trace74ConditionalSaturationGuard','Trace74DirectFourBlock','Trace74BoundaryConcreteZero','Trace74BoundarySeedModelFacts','Trace74BoundarySeedSpecialization','Trace74BoundaryGenericAssembly','Trace74BoundaryGenericCastTransfer','Trace74BoundaryNaturalSeed','Trace74BoundaryRecurrenceCast','Trace74BoundarySeedParametric','Trace74BoundaryGraphWitness','Trace74BoundaryGraph','Trace75BFSFixedIPRA','Trace75BFSModelHalt','Trace75BFSHaltGraph'):
  need(summaries[saved]==parent['closures'][saved],'saved closure set changed '+saved)
  for dep in summaries[saved]['project']:need(dep in parent['selected_project'] and hashes(objects[dep])==hashes(parent['selected_project'][dep]),'saved closure companion changed '+dep)
  for dep in summaries[saved]['outside']:need(dep in parent['selected_outside'] and hashes(ext[dep])==hashes(parent['selected_outside'][dep]),'saved outside companion changed '+dep)
 for r in rows:
  actual_imports=heads[r['module']];need(header_matches(actual_imports,r['imports']),'forward serialized source imports changed '+r['module'])
 for n,rec0 in ext.items():need(n in outside_now and hashes(rec0)==hashes(outside_now[n]),'unrecorded outside closure '+n)
 stable_inputs();stable_base();stable_outside();stable_union(expected)
 result.update({'status':'PASS','selected_project':objects,'selected_outside':ext,'serialized_headers':heads,'header_reuse':sorted(reused),'closures':summaries,'union_count':len(expected),'postflight':resources()});save()
 print(json.dumps({'status':'PASS','root':str(root),'stages':len(order),'result_sha256':sha(O/'result.json')}))
except BaseException as e:
 result.update({'status':'FAILED','exception':repr(e),'traceback':traceback.format_exc(),'postflight':resources()});save();raise
