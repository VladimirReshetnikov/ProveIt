#!/usr/bin/env python3
"""Two translated-consistency corollaries over the audited fresh P72 build."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];OUT=Path('/tmp/p72-p13-p14-translated-fresh-20261105');FRESH=Path('/tmp/p72-current-base-extension-attempt02-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';REVIEW=D/'reviews/p72-current-base-extension-attempt02-independent';TERMINAL=D/'research/p72-current-base-extension-build-attempt02/terminal';roots=[FRESH/'lib',PKG,TOOL];SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
def save():
 p=OUT/'state.tmp';p.write_text(json.dumps(state,sort_keys=True,indent=2)+'\n');os.replace(p,OUT/'state.json')
def no_lean():
 for p in Path('/proc').iterdir():
  if not p.name.isdecimal():continue
  try:
   if (p/'comm').read_text().strip()=='lean' and (p/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X'):return False
  except (FileNotFoundError,ProcessLookupError):continue
 return True
def available():
 for line in Path('/proc/meminfo').read_text().splitlines():
  if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
 raise RuntimeError('missing MemAvailable')
pins={P/'P72Translated.lean':'324803ca69036a8731c1bb9a65fd635e8a48d29a998c57023eef8f6f1901691a',P/'monitor.py':'d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad',P/'controls.py':'549acb06c7e0a8a80545c4a2e6143ce8b0730974407fe3e9e8382c367ca31c4f',P/'controls-result.json':'11eb2364388e53a42fd9d3175a3b7255f29581093207d7d89257bdc0c8336fd5',REVIEW/'check.py':'b33ae7fa683212592da52d7fc041a1b76381e7c6681f58f8ebcd53240642bd0f',REVIEW/'result.json':'a8eb52729db2c06ef98cb0b906efed0f63ab492f04a32d0cf40d1c4f6dd5b595',TERMINAL/'progress.json':'f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a',TERMINAL/'outer-terminal.json':'a0cad18c8a85f74f1d69f57b7c510fa56a488726c66cbfc96421f88476acfa07',FRESH/'lib/DiophantineConsistency/Compact44/IPRAOrdinary72.olean':'ef08b9c68b1f7a770f698b14fc65d221c7db399d924b69c9a3aa9e978464a48a',FRESH/'lib/DiophantineConsistency/Compact44/IPRAOrdinary72P14.olean':'ca06ffe7d590b250f7585ae75f7aa4a8d9c6e8a12b14096dc56ec55caeed41aa',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
def guard(names):
 out={}
 for n in sorted(names):
  for root in roots:
   for suffix in SUF:
    p=root/(n.replace('.','/')+suffix)
    if os.path.lexists(p):need(p.is_file(),'bad candidate '+str(p));out[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
    else:out[str(p)]=None
 return out
def preflight():
 for p,h in pins.items():need(p.is_file() and sha(p)==h,'input drift '+str(p))
 need(sha(FRESH/'progress.json')==pins[TERMINAL/'progress.json'],'fresh progress drift');o=json.loads((TERMINAL/'outer-terminal.json').read_bytes());need(o['actual_session']==92122 and o['exit_code']==0,'fresh outer observation')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(REVIEW/'check.py')],capture_output=True,timeout=600);need(q.returncode==0 and not q.stderr and q.stdout==(REVIEW/'result.json').read_bytes(),'independent 681-stage review did not reproduce')
 need(available()>=10*1024**3 and shutil.disk_usage('/tmp').free>=5_000_000_000,'resource preflight')
 return {'audit_stdout_sha256':hashlib.sha256(q.stdout).hexdigest()}
need(not OUT.exists() and no_lean(),'output exists or Lean active');runner=sha(__file__);before=preflight()
if sys.argv[1:]==['--preflight']:
 print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','audit_stdout_sha256':before['audit_stdout_sha256'],'scope':'No Lean; single prior fresh-source artifact audit reproduced.'},sort_keys=True));raise SystemExit(0)
need(not sys.argv[1:],'unexpected arguments');OUT.mkdir();state={'status':'RUNNING','runner_sha256':runner,'preflight_before':before,'pins':{str(k):v for k,v in pins.items()},'scope':'Fresh-project P13/P14 translated endpoints; inherited base/package/dynamic and sampled-resource limits remain. No Lean JSON or file semantics.'};save()
spec=importlib.util.spec_from_file_location('mon',P/'monitor.py');mon=importlib.util.module_from_spec(spec);spec.loader.exec_module(mon)
try:
 source=OUT/'P72Translated.lean';shutil.copyfile(P/'P72Translated.lean',source);need(sha(source)==pins[P/'P72Translated.lean'],'source copy');env=dict(os.environ,LEAN_PATH=str(FRESH/'lib')+':'+str(PKG),LEAN_NUM_THREADS='1')
 for k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(k,None)
 prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M4000','-j1','-DElab.async=false'];obj=OUT/'P72Translated.olean';state['runs']=[]
 for typ,args in [('deps',['--deps',str(source)]),('compile',['--root='+str(OUT),str(source),'-o',str(obj)])]:
  log=OUT/(typ+'.txt');m=mon.run(prefix+args,OUT,env,log,rss_limit=5*1024**3,mem_floor=10*1024**3,seconds=180,interval=.1);state['runs'].append({'command':prefix+args,**m,'log_sha256':sha(log)});save();need(m['exit']==0 and m['stop_reason'] is None and not m['monitor_errors'] and not m['observed_descendant_pids'],'Lean '+typ+' failure')
  if typ=='deps':
   actual={};counts={}
   for line in log.read_text().splitlines():
    p=Path(line);hits=[r for r in roots if p.is_relative_to(r)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(hits)==1,'bad dependency');n=str(p.relative_to(hits[0]))[:-6].replace('/','.');counts[n]=counts.get(n,0)+1;need(n not in actual or (n=='Init' and counts[n]<=2 and actual[n]['path']==line),'duplicate dependency '+n);actual[n]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
   need(set(actual)-{'Init'}=={'DiophantineConsistency.Compact44.IPRAOrdinary72P14'},'unexpected imports');n='DiophantineConsistency.Compact44.IPRAOrdinary72P14';need(actual[n]['path']==str(FRESH/'lib'/Path(*n.split('.')).with_suffix('.olean')) and actual[n]['sha256']==pins[FRESH/'lib/DiophantineConsistency/Compact44/IPRAOrdinary72P14.olean'],'P14 route');state['dependencies']=actual;state['direct_guard']=guard(actual);save()
 text=(OUT/'compile.txt').read_text();need(not re.search(r'(?im)^.*(?:error:|sorryAx|declaration uses .sorry.).*$',text) and obj.is_file(),'compile error')
 for n in ('standard_translated_p13','standard_translated_p14'):
  reports=re.findall(r"'DiophantineConsistency.P72Translated."+n+r"' depends on axioms: \[([^]]*)\]",text);need(len(reports)==1 and set(x.strip() for x in reports[0].split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},'axiom report '+n)
 need(guard(state['dependencies'])==state['direct_guard'],'guard drift');state['preflight_after']=preflight();need(state['preflight_after']==before and sha(__file__)==runner,'preflight/runner drift');state['object_sha256']=sha(obj);state['status']='PASS';save();print('PASS fresh P13/P14 translated consistency',flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
