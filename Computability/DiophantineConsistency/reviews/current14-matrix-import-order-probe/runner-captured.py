#!/usr/bin/env python3
"""Two guarded import-only checks, exact captured provider; no repo mutation."""
import hashlib,importlib.util,json,os,shutil,subprocess,sys,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires -I -S -B')
root=Path('/tmp/current14-matrix-order-probe-20261104');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');helper=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-structured-endpoint-coherent-runner-v3/owned.py')
pins={lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',helper:'51f3ec69c2f4a11cfe118072f724a110c976a3557d1c68553ebb6a9c8108f498',pkg/'Foundation/Vorspiel/Matrix.olean':'60d88293f7d5e99f62d89a56697e6056b13725fe524f1602bf2a39939f091550',pkg/'Mathlib/LinearAlgebra/Matrix/InvariantBasisNumber.olean':'a6d4cc91ce5cacdb396c1a18de7cc7ed9e378a37a9f48feb9ebdabb395eb0c3a'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,s):
 if not b:raise RuntimeError(s)
def mem():
 for line in Path('/proc/meminfo').read_text().splitlines():
  if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
 raise RuntimeError('MemAvailable unavailable')
def guard():
 for p,h in pins.items():need(p.is_file() and sha(p)==h,'pin mismatch '+str(p))
 r={}
 for obj in list(pins)[2:]:
  stem=str(obj)[:-6]
  for suffix in ('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash'):
   p=Path(stem+suffix)
   if os.path.lexists(p):need(p.is_file(),'invalid companion '+str(p));r[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
   else:r[str(p)]=None
 return r
def idle():
 ps=subprocess.run(['ps','-eo','pid=,stat=,comm='],check=True,text=True,stdout=subprocess.PIPE).stdout
 return not any(len(x)==3 and x[2]=='lean' and not x[1].startswith('Z') for x in (line.split() for line in ps.splitlines()))
need(mem()>=10*1024**3 and shutil.disk_usage('/tmp').free>=4_000_000_000 and idle(),'preflight resource/slot')
spec=importlib.util.spec_from_file_location('matrix_probe_owned',helper);owned=importlib.util.module_from_spec(spec);spec.loader.exec_module(owned)
before=guard();runner_sha=sha(__file__);results=[]
env=dict(os.environ,LEAN_PATH=str(pkg),LEAN_NUM_THREADS='1')
for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
for label,mods in [('foundation_first',['Foundation.Vorspiel.Matrix','Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber']),('mathlib_first',['Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber','Foundation.Vorspiel.Matrix'])]:
 need(idle() and mem()>=10*1024**3 and shutil.disk_usage('/tmp').free>=4_000_000_000,'preflight per case')
 case=root/label;case.mkdir();src=case/'Probe.lean';src.write_text(''.join('import '+m+'\n' for m in mods));obj=case/'Probe.olean';stdout=case/'stdout.log';stderr=case/'stderr.log';events=[];samples=[]
 def check(pid):
  total=0
  for child in owned.group_live(pid):
   try:total+=int(Path('/proc',str(child),'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
   except FileNotFoundError:pass
  current={'session_rss':total,'available':mem(),'free':shutil.disk_usage('/tmp').free};samples.append(current)
  return total<7*1024**3//2 and current['available']>=10*1024**3 and current['free']>=4_000_000_000
 cmd=['/usr/bin/ionice','-c','3','nice','-n','19',str(lean),'-M3000','-j1','-DElab.async=false','--root='+str(case),str(src),'-o',str(obj)]
 failure=None;code=None;receipt=None
 with stdout.open('x') as o,stderr.open('x') as e:
  try:code,seconds,receipt=owned.run(cmd,cwd=case,env=env,stdout=o,stderr=e,timeout=60,disk_check=check,report=events.append,poll_interval=.25)
  except BaseException as exc:failure=repr(exc);seconds=None
 need(samples and guard()==before and sha(__file__)==runner_sha,'guard/sample drift')
 rec={'case':label,'imports':mods,'command':cmd,'exit':code,'monitor_failure':failure,'owned_receipt':receipt,'seconds':seconds,'events':events,'samples':len(samples),'peak_rss':max(s['session_rss'] for s in samples),'min_available':min(s['available'] for s in samples),'source_sha256':sha(src),'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr),'object_sha256':sha(obj) if obj.is_file() else None}
 results.append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 if failure is not None:break
need(guard()==before and sha(__file__)==runner_sha,'final guards')
result={'status':'COMPLETED_BOTH' if len(results)==2 and all(x['monitor_failure'] is None for x in results) else 'INTERRUPTED','runner_sha256':runner_sha,'provider_guards':before,'results':results,'scope':'Two import-only checks, single observed child each; direct provider companions pinned, transitive/dynamic ancestry inherited. No endpoint theorem.'}
with (root/'result.json').open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
print('PROBE_RESULT',result['status'],flush=True)
