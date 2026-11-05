#!/usr/bin/env python3
"""Bounded seed-construction helper against authenticated invariant lemma."""
import hashlib,json,os,re,shutil,subprocess,sys,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1];ROOT=next(p for p in HERE.parents if (p/'lakefile.toml').is_file());PKT=TASK/'research/thirteen-current2011-fresh-model';PROD=Path('/tmp/thirteen-current2011-fresh-model-build-20261105');OLD=Path('/tmp/normalized106-fresh-model-build-v2-20261105/lib');OUT=Path('/tmp/thirteen-seed-construction-check-20261105');SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';PREF=PKT/'preflight.py';MAN=PKT/'preflight-result.json';roots=[OUT/'lib',SPHERE,MODEL,PKG,TOOL];SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
def save():
 p=OUT/'state.tmp';p.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');os.replace(p,OUT/'state.json')
def available():
 for line in Path('/proc/meminfo').read_text().splitlines():
  if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
 raise RuntimeError('MemAvailable missing')
def no_lean():
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   if (p/'comm').read_text().strip()=='lean' and (p/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X'):return False
  except (FileNotFoundError,ProcessLookupError):continue
 return True
def preflight():
 need(sha(PREF)=='d61f973a63f89ceb8057ad3c1bf5e652101b9102b0dfc064574cc04d8149c062' and sha(MAN)=='a796fa2f7752939d862520b50e76fd8fc2f6bbfcdc5cc4337959d94b576a3f0e','preflight pins')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PREF),'--existing-output'],cwd=ROOT,capture_output=True,timeout=600);need(q.returncode==0 and not q.stderr and q.stdout==MAN.read_bytes(),'preflight mismatch '+q.stderr.decode(errors='replace')[-500:]);return hashlib.sha256(q.stdout).hexdigest()
def checkprior():
 need(sha(PROD/'state.json')==sha(PKT/'attempt01/state.json')=='18313c0e4228fc842c9d6dfa0064b4b21467531e4bab63d3902a3eb60733e15b','prior state');d=json.loads((PROD/'state.json').read_text());need(d['status']=='FAILED' and len(d['records'])==7 and d['active']['module']=='DiophantineConsistency.ModelThirteenCarrier','prior scope')
 for rec in d['records']:
  n=rec['module'];p=PROD/'src'/(n.replace('.','/')+'.lean');o=PROD/'lib'/(n.replace('.','/')+'.olean');need(rec['compile_run']['exit']==0 and sha(p)==rec['source_sha256'] and sha(o)==rec['object_sha256'],'prior source/object '+n)
  for k in ('compile_run','deps_run'):need(sha(rec[k]['log'])==rec[k]['log_sha256'],'prior log '+n)
  for path,v in rec['direct_guard'].items():
   q=Path(path)
   if v is None:need(not os.path.lexists(q),'prior absent input '+path)
   else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'prior changed input '+path)
 links={}
 for root,dirs,files in os.walk(OLD,followlinks=False,onerror=lambda e:(_ for _ in ()).throw(e)):
  rr=Path(root);need(not any((rr/x).is_symlink() for x in dirs),'base symlink directory')
  for x in files:
   src=rr/x;target=PROD/'lib'/src.relative_to(OLD);need(src.is_file() and target.is_symlink() and target.resolve()==src.resolve(),'base link '+str(target));links[str(target)]=str(src.resolve())
 need(len(links)==d['base_link_count']==1016 and hashlib.sha256(json.dumps(links,sort_keys=True).encode()).hexdigest()==d['base_links_sha256'],'base inventory')
 return d
def guard(names):
 result={}
 for n in sorted(names):
  for root in roots:
   for suffix in SUFFIXES:
    p=root/(n.replace('.','/')+suffix)
    if os.path.lexists(p):need(p.is_file(),'bad candidate '+str(p));result[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
    else:result[str(p)]=None
 return result
CORE=Path('/tmp/thirteen-carrier-split-core-20261105');SPLIT=TASK/'research/thirteen-current2011-carrier-split-draft';PRELUDE=Path('/tmp/thirteen-carrier-model-prelude-20261105');PREPKT=TASK/'research/thirteen-current2011-carrier-model-prelude-diagnostic'
def checkcore():
 need(sha(CORE/'state.json')==sha(SPLIT/'attempt01/state.json')=='442fc30b210d475f8b3de2f5b9910fe515849c0a80d91d196b39cc9881a29973','core state drift')
 d=json.loads((CORE/'state.json').read_text());need(d['status']=='PASS' and len(d['runs'])==2 and all(x['exit']==0 for x in d['runs']),'core run status')
 need(sha(CORE/'DiophantineConsistency/ModelThirteenCarrierCore.lean')==sha(SPLIT/'src/DiophantineConsistency/ModelThirteenCarrierCore.lean')=='394d7b25748bb93ac285f6bac763d948364ce12277a6ccf999dc6915f3864dc9','core source')
 need(sha(CORE/'lib/DiophantineConsistency/ModelThirteenCarrierCore.olean')==d['object_sha256']=='023005d35e7c8a460213270f9b7ec013954b1010c9d80945db918baee919d319','core object')
 need(sha(CORE/'deps.txt')==d['runs'][0]['log_sha256'] and sha(CORE/'compile.txt')==d['runs'][1]['log_sha256'],'core logs')
 for path,v in d['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'core absent input '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'core input drift '+path)
def checkprelude():
 need(sha(PRELUDE/'state.json')==sha(PREPKT/'attempt01/state.json')=='3846ce468421358eade614d2651a45d9db0037f0e46d303a92e7b54222d4fd2a','prelude state')
 d=json.loads((PRELUDE/'state.json').read_text());need(d['status']=='PASS' and len(d['runs'])==2 and all(r['exit']==0 for r in d['runs']),'prelude status')
 need(sha(PRELUDE/'DiophantineConsistency/ModelThirteenCarrierPrelude.lean')==sha(PREPKT/'ModelThirteenCarrierPrelude.lean')=='c3a5c6047f9f72d7d5663fa2ad047f00754b5ea92208b6a04ae997714124acc8','prelude source')
 need(sha(PRELUDE/'lib/DiophantineConsistency/ModelThirteenCarrierPrelude.olean')==d['object_sha256']=='918f5fc28b61155bfc417f5ce50d1a5fde0023198c1b3779937768bbb9414bff','prelude object')
 need(sha(PRELUDE/'deps.txt')==d['runs'][0]['log_sha256'] and sha(PRELUDE/'compile.txt')==d['runs'][1]['log_sha256'],'prelude logs')
 for path,v in d['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'prelude absent input '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'prelude input drift '+path)
 for path,target in d['overlay_links'].items():
  q=Path(path);need(q.is_symlink() and q.is_file() and str(q.resolve())==target,'prelude overlay '+path)
HELPERS=[
 ('ModelThirteenCoreInvariants', TASK/'research/thirteen-current2011-core-invariants-draft',Path('/tmp/thirteen-core-invariants-check-20261105'),'b8da4543225cefb27c28573215589f9ed1c2d57aad6e34379d0296096ae4f197','2e30e6042941ac449c68e1db49cc2aee818098a823e1c2e51a81198671d3e9c8','3a4a7d8b04de145836ef2ccdfdd6cdf84cfc4c728caf5a4ec64785eb85c1a467'),
 ('ModelThirteenRankOrdinate', TASK/'research/thirteen-current2011-rank-ordinate-draft',Path('/tmp/thirteen-rank-ordinate-check-20261105'),'55a477d517914a577be497963800661d31775fd0e81cb14e5f84e700527871cb','5809fb104c3c59e973c967d901c58ad6546ae463a225e8ec9a9e080751f620f2','07fe448925823258ff75480a6bc775eb2b46566654c67906f97a8be59052b6f7')]
def checkhelpers():
 for n,pkt,base,st,src,obj in HELPERS:
  need(sha(base/'state.json')==sha(pkt/'attempt01/state.json')==st,'helper state '+n)
  d=json.loads((base/'state.json').read_text());need(d['status']=='PASS' and len(d['runs'])==2 and all(x['exit']==0 for x in d['runs']),'helper status '+n)
  need(sha(base/'DiophantineConsistency'/(n+'.lean'))==sha(pkt/(n+'.lean'))==src,'helper source '+n)
  need(sha(base/'lib/DiophantineConsistency'/(n+'.olean'))==d['object_sha256']==obj,'helper object '+n)
  need(sha(base/'deps.txt')==d['runs'][0]['log_sha256'] and sha(base/'compile.txt')==d['runs'][1]['log_sha256'],'helper logs '+n)
  for path,v in d['direct_guard'].items():
   q=Path(path)
   if v is None:need(not os.path.lexists(q),'helper absent input '+path)
   else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'helper input drift '+path)
  for path,target in d['overlay_links'].items():
   q=Path(path);need(q.is_symlink() and q.is_file() and str(q.resolve())==target,'helper overlay '+path)
def makeoverlay():
 links={}; base=PROD/'lib'
 for root,dirs,files in os.walk(base,followlinks=False,onerror=lambda e:(_ for _ in ()).throw(e)):
  rr=Path(root);need(not any((rr/x).is_symlink() for x in dirs),'overlay source symlink directory')
  for name in files:
   p=rr/name;need(p.is_file(),'overlay source file');q=OUT/'lib'/p.relative_to(base);q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p.resolve());links[str(q)]=str(p.resolve())
 core=CORE/'lib/DiophantineConsistency/ModelThirteenCarrierCore.olean'; dest=OUT/'lib/DiophantineConsistency/ModelThirteenCarrierCore.olean';need(not os.path.lexists(dest),'core shadow');dest.symlink_to(core.resolve());links[str(dest)]=str(core.resolve())
 pre=PRELUDE/'lib/DiophantineConsistency/ModelThirteenCarrierPrelude.olean';dest=OUT/'lib/DiophantineConsistency/ModelThirteenCarrierPrelude.olean';need(not os.path.lexists(dest),'prelude shadow');dest.symlink_to(pre.resolve());links[str(dest)]=str(pre.resolve())
 for n,pkt,base,st,src,obj in HELPERS:
  srcobj=base/'lib/DiophantineConsistency'/(n+'.olean');dest=OUT/'lib/DiophantineConsistency'/(n+'.olean');need(not os.path.lexists(dest),'helper shadow');dest.symlink_to(srcobj.resolve());links[str(dest)]=str(srcobj.resolve())
 state['overlay_links']=links;save()
def checkoverlay():
 observed={}
 for root,dirs,files in os.walk(OUT/'lib',followlinks=False,onerror=lambda e:(_ for _ in ()).throw(e)):
  rr=Path(root);need(not any((rr/x).is_symlink() for x in dirs),'overlay symlink directory')
  for name in files:
   q=rr/name
   if q==OUT/'lib/DiophantineConsistency/ModelThirteenSeedConstruction.olean':continue
   need(q.is_symlink() and q.is_file(),'overlay altered '+str(q));observed[str(q)]=str(q.resolve())
 need(observed==state['overlay_links'],'overlay inventory drift')
need(not OUT.exists() and no_lean(),'output exists or Lean active');need(available()>=10*1024**3 and shutil.disk_usage('/tmp').free>=5_000_000_000,'resource preflight');need(sha(HERE/'ModelThirteenSeedConstruction.lean')=='06f00485f5991ff193561f2d6c5da33e11ba554f7a75247534f04ffe421752f1','source pin');runner=sha(__file__);presh=preflight();prior=checkprior();OUT.mkdir();state={'status':'RUNNING','runner_sha256':runner,'preflight_before_sha256':presh,'prior_state_sha256':sha(PROD/'state.json'),'scope':'Seed construction helper only; no completion or endpoint; no new base rebuild, dynamic/package-transitive load trace, automatic group-RSS or host-memory stop. GNU foreground timeout controls only its direct child.'};save()
try:
 checkhelpers();checkprelude();checkcore(); source=OUT/'DiophantineConsistency/ModelThirteenSeedConstruction.lean';source.parent.mkdir();shutil.copyfile(HERE/'ModelThirteenSeedConstruction.lean',source);need(sha(source)==sha(HERE/'ModelThirteenSeedConstruction.lean'),'source copy');makeoverlay();imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',source.read_text(),re.M);need(imports==['DiophantineConsistency.ModelThirteenCoreInvariants'],'unexpected imports');env=dict(os.environ,LEAN_PATH=':'.join(map(str,roots[:-1])),LEAN_NUM_THREADS='1')
 for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
 prefix=['/usr/bin/timeout','--foreground','--signal=TERM','--kill-after=5s','180s','/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M2800','-j1','-DElab.async=false'];state['runs']=[]
 for i,name in enumerate(('deps','compile')):
  need(available()>=10*1024**3 and shutil.disk_usage(OUT).free>=5_000_000_000,'stage resources');args=['--deps',str(source)] if i==0 else ['--root='+str(OUT),str(source),'-o',str(OUT/'lib/DiophantineConsistency/ModelThirteenSeedConstruction.olean')];start=time.monotonic();log=OUT/(name+'.txt')
  with log.open('x') as f:q=subprocess.run(prefix+args,cwd=OUT,env=env,stdout=f,stderr=subprocess.STDOUT)
  state['runs'].append({'command':prefix+args,'exit':q.returncode,'seconds':round(time.monotonic()-start,3),'log_sha256':sha(log)});save();need(q.returncode==0,'Lean '+name+' failed')
  if i==0:
   actual={};counts={}
   for line in log.read_text().splitlines():
    p=Path(line);hits=[r for r in roots if p.is_relative_to(r)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(hits)==1,'invalid dependency');mod=str(p.relative_to(hits[0]))[:-6].replace('/','.');counts[mod]=counts.get(mod,0)+1;need(mod not in actual or (mod=='Init' and counts[mod]<=2 and actual[mod]['path']==line),'duplicate dependency');actual[mod]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
   need(set(actual)-{'Init'}==set(imports)-{'Init'},'unexpected dependency names')
   for mod,rec in actual.items():
    candidates=[r/(mod.replace('.','/')+'.olean') for r in roots if (r/(mod.replace('.','/')+'.olean')).is_file()]
    need(candidates and str(candidates[0])==rec['path'],'dependency route '+mod)
   need(actual['DiophantineConsistency.ModelThirteenCoreInvariants']['path']==str(OUT/'lib/DiophantineConsistency/ModelThirteenCoreInvariants.olean'),'helper route')
   state['dependencies']=actual;state['direct_guard']=guard(actual);save()
 text=(OUT/'compile.txt').read_text();need(not re.search(r'(?im)^.*(?:error:|sorryAx|declaration uses .sorry.).*$',text),'compile error or placeholder');reports=re.findall(r"'DiophantineConsistency.ModelThirteenCarrier.seed_construction' depends on axioms: \[([^]]*)\]",text);need(len(reports)==1 and set(x.strip() for x in reports[0].split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},'seed axiom report');need((OUT/'lib/DiophantineConsistency/ModelThirteenSeedConstruction.olean').is_file(),'missing object');state['object_sha256']=sha(OUT/'lib/DiophantineConsistency/ModelThirteenSeedConstruction.olean');need(guard(state['dependencies'])==state['direct_guard'],'direct guard drift');checkoverlay();checkhelpers();checkprelude();checkcore();checkprior();state['preflight_after_sha256']=preflight();need(sha(__file__)==runner,'runner changed');state['status']='PASS';save();print('PASS seed-construction helper',flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
