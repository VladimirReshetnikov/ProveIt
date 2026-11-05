#!/usr/bin/env python3
"""Bounded combined-import probe; no project module is rebuilt."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];OUT=Path('/tmp/p72-current-base-external-import-probe-20261105');BASE=Path('/tmp/current14-standard-fresh-build-20261104/lib');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';OLD=D/'research/normalized106-combined-import-probe/runner.py';roots=[BASE,PKG,TOOL];SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
def save():
 p=OUT/'state.tmp';p.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');os.replace(p,OUT/'state.json')
def no_lean():
 for p in Path('/proc').iterdir():
  if not p.name.isdecimal():continue
  try:
   if (p/'comm').read_text().strip()=='lean' and (p/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X'):return False
  except (FileNotFoundError,ProcessLookupError):continue
 return True
pins={P/'P72ExternalImports.lean':'084065e7503aca970b0874e12c83e78827ba03387143dbfb8e2ecdb129be5d83',P/'monitor.py':'d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad',OLD:'ed5f3f1bf138e5ae3586dd9c7c1ae4b46b4f2065de7b9295e4c827b7cc935866',BASE/'DiophantineConsistency/IPRAStandardCurrentEndpoint.olean':'3b8abcafa1fad691d9a9005e2af8afae8bda77c7d761a00119ccea1c742dcbd2',PKG/'Mathlib/Data/Fintype/BigOperators.olean':'e9e47e19312252f1f7e73800173cc8e4a5001517a7f385665af244b0423c998e',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
imports=['DiophantineConsistency.IPRAStandardCurrentEndpoint','Mathlib.Algebra.MvPolynomial.CommRing','Mathlib.Algebra.Order.Ring.Cone','Mathlib.Data.Fintype.BigOperators']
def guard(names):
 result={}
 for n in sorted(names):
  for root in roots:
   for suffix in SUF:
    f=root/(n.replace('.','/')+suffix)
    if os.path.lexists(f):need(f.is_file(),'bad candidate '+str(f));result[str(f)]={'realpath':str(f.resolve()),'sha256':sha(f)}
    else:result[str(f)]=None
  available=[root/(n.replace('.','/')+'.olean') for root in roots if (root/(n.replace('.','/')+'.olean')).is_file()]
  need(available and len({sha(f) for f in available})==1,'missing or conflicting provider '+n)
 return result
def preflight():
 for p,h in pins.items():need(p.is_file() and sha(p)==h,'pin drift '+str(p))
 q=subprocess.run([sys.executable,'-I','-S','-B',str(OLD),'--preflight'],capture_output=True,timeout=180);need(q.returncode==0 and not q.stderr,'earlier current14 preflight failed')
 return {'earlier_preflight_sha256':hashlib.sha256(q.stdout).hexdigest(),'direct':guard(imports+['Init'])}
need(not OUT.exists() and no_lean(),'output exists or Lean active');need(shutil.disk_usage('/tmp').free>=5_000_000_000,'disk floor');runner=sha(__file__);before=preflight();OUT.mkdir();state={'status':'RUNNING','runner_sha256':runner,'preflight_before':before,'scope':'One current-base combined import diagnostic only; no project rebuild, package-transitive closure, or Lean equation theorem. Sampled guards may miss transient spikes or escaped descendants.'};save()
spec=importlib.util.spec_from_file_location('mon',P/'monitor.py');mon=importlib.util.module_from_spec(spec);spec.loader.exec_module(mon)
try:
 source=OUT/'P72ExternalImports.lean';shutil.copyfile(P/'P72ExternalImports.lean',source);need(sha(source)==pins[P/'P72ExternalImports.lean'],'source copy');env=dict(os.environ,LEAN_PATH=str(BASE)+':'+str(PKG),LEAN_NUM_THREADS='1')
 for k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(k,None)
 prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M4000','-j1','-DElab.async=false'];state['runs']=[]
 for typ,args in [('deps',['--deps',str(source)]),('compile',['--root='+str(OUT),str(source),'-o',str(OUT/'P72ExternalImports.olean')])]:
  log=OUT/(typ+'.txt');m=mon.run(prefix+args,OUT,env,log,rss_limit=5*1024**3,mem_floor=10*1024**3,seconds=180,interval=.1);state['runs'].append({'command':prefix+args,**m,'log_sha256':sha(log)});save();need(m['exit']==0 and m['stop_reason'] is None and not m['monitor_errors'] and not m['observed_descendant_pids'],'Lean '+typ+' failure')
  if typ=='deps':
   found={};counts={}
   for line in log.read_text().splitlines():
    f=Path(line);hits=[r for r in roots if f.is_relative_to(r)];need(f.is_file() and f.is_absolute() and line.endswith('.olean') and len(hits)==1,'invalid dep');n=str(f.relative_to(hits[0]))[:-6].replace('/','.');counts[n]=counts.get(n,0)+1;need(n not in found or (n=='Init' and counts[n]<=2 and found[n]['path']==line),'duplicate dep');found[n]={'path':line,'realpath':str(f.resolve()),'sha256':sha(f)}
   need(set(found)-{'Init'}==set(imports),'dependency mismatch')
   for n,v in found.items():
    first=next(r/(n.replace('.','/')+'.olean') for r in roots if (r/(n.replace('.','/')+'.olean')).is_file());need(str(first)==v['path'],'route '+n)
   state['dependencies']=found;save()
 need((OUT/'compile.txt').read_text()=='True : Prop\n' and (OUT/'P72ExternalImports.olean').is_file(),'unexpected output');state['object_sha256']=sha(OUT/'P72ExternalImports.olean');state['preflight_after']=preflight();need(state['preflight_before']==state['preflight_after'] and sha(__file__)==runner,'preflight or runner drift');state['status']='PASS';save();print('PASS P72 current-base external import probe',flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
