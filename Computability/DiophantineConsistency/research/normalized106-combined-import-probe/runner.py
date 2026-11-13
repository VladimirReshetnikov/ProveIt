#!/usr/bin/env python3
"""Two bounded import diagnostics. --preflight and --selftest never launch Lean."""
import hashlib,importlib.util,json,os,re,shutil,sys,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;RESEARCH=HERE.parent;ROOT=next(x for x in HERE.parents if (x/'lakefile.toml').is_file())
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');BASE=Path('/tmp/current14-standard-fresh-build-20261104/lib');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');ROOTS=(BASE,PACKAGE,TOOL)
OUT=Path('/tmp/normalized106-combined-import-probe-20261105');HELPER=HERE/'owned.py';PREFLIGHT=RESEARCH/'normalized106-current14-sixteen-source-preflight/result.json';DIRECT=RESEARCH/'nine-variable-external-matrix-preflight/direct-result.json';STATE=Path('/tmp/current14-standard-fresh-build-20261104/state.json')
SOURCES={'endpoint':HERE/'EndpointPlusExternal.lean','matrix':HERE/'MatrixPlusExternal.lean'}
EXTRA=['Mathlib.Algebra.MvPolynomial.CommRing','Mathlib.Algebra.Order.Ring.Abs','Mathlib.Algebra.Order.Ring.Cone','Mathlib.Data.Int.Basic','Mathlib.Data.Int.Order.Units'];ENDPOINT='DiophantineConsistency.IPRAStandardCurrentEndpoint';MATRIX='Foundation.Vorspiel.Matrix';NAMES=[ENDPOINT,MATRIX]+EXTRA
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
PINS={Path('/tmp/current14-standard-fresh-source-20261104/src/DiophantineConsistency/IPRAStandardCurrentEndpoint.lean'):'756d87adb5a9cb8e192156b043714f55afe3836d7833ef87d5113cba8d772c38',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',HELPER:'a41aee499bcef7b6ece79e1e7eae2b99210a70c1dafc1e54f2de55fbfc8d6201',PREFLIGHT:'f159489a58b1804d327a35b98ae75e64d746efe4605de0ce8a25ef3d92ca70b2',DIRECT:'8fc9a8a1978eecd0ddfb58928a5f2aa113a0a757dd4e7b63d1aeb120df76f787',STATE:'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',SOURCES['endpoint']:'31aa8357e3b93245b71ffb41ad8c83b9897e1271f83dc478b922eb9c6b10ba2e',SOURCES['matrix']:'f31db847dd1b042c5b3f772e64acf13c9a0f91bfe42971afdb039964009ae722'}
SHA=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def need(b,msg):
 if not b:raise RuntimeError(msg)
def parse_imports(text):return re.findall(r'^import ([A-Za-z0-9_.]+)$',text,re.M)
def assert_equal(expected,actual,label):need(expected==actual,label)
def within_limits(available,rss,free):return available>=10*1024**3 and rss<7*1024**3//2 and free>=512*1024**2
def inspect(path):
 if not os.path.lexists(path):return None
 need(path.is_file(),'invalid candidate '+str(path));st=path.stat()
 return {'realpath':str(path.resolve()),'sha256':SHA(path),'size':st.st_size,'mtime_ns':st.st_mtime_ns}
def imports_valid():
 assert_equal([ENDPOINT]+EXTRA,parse_imports(SOURCES['endpoint'].read_text()),'endpoint probe imports')
 assert_equal([MATRIX]+EXTRA,parse_imports(SOURCES['matrix'].read_text()),'matrix probe imports')
def direct_guard():
 need(not any(not x.is_dir() for x in ROOTS),'missing root')
 previous=json.loads(DIRECT.read_bytes());basis=json.loads(PREFLIGHT.read_bytes());base=json.loads(STATE.read_bytes())
 need(previous['status']=='PASS_DIRECT_DEPS_NOT_IMPORT_CHECK' and previous['exit']==0 and previous['guards_before']==previous['guards_after'],'old direct probe not clean')
 need(basis['status']=='PASS_SOURCE_DECLARED_PREFLIGHT_NOT_BUILD_AUTHORIZATION' and basis['new_declared_external']==EXTRA,'source survey mismatch')
 need(base['status']=='PASS' and base['source_status']=='CURRENT_AT_FINAL_CHECK','base status')
 rec=next(x for x in base['records'] if x['module']==ENDPOINT)
 need(rec['exit']==0 and rec['object_sha256']=='3b8abcafa1fad691d9a9005e2af8afae8bda77c7d761a00119ccea1c742dcbd2' and rec['source_sha256']==PINS[Path('/tmp/current14-standard-fresh-source-20261104/src/DiophantineConsistency/IPRAStandardCurrentEndpoint.lean')],'base endpoint producer')
 need(SHA(Path(rec['log']))==rec['log_sha256'],'base endpoint log drift')
 for entry in rec['direct_inputs'].values():need(SHA(Path(entry['path']))==entry['sha256'],'base endpoint direct drift '+entry['path'])
 out={}
 for name in NAMES:
  stem=Path(*name.split('.'))
  for idx,root in enumerate(ROOTS):
   for suffix in SUFFIXES:
    f=root/(str(stem)+suffix);v=inspect(f);out[str(f)]=v
    if name==ENDPOINT:
     if idx==0:
      recorded=base['outputs'][name].get(str(f),'MISSING');need(recorded!='MISSING','endpoint inventory missing '+str(f))
      if recorded is None:need(v is None,'unexpected endpoint companion '+str(f))
      else:need(v is not None and v['realpath']==recorded['realpath'] and v['sha256']==recorded['sha256'],'endpoint artifact mismatch '+str(f))
     else:need(v is None,'endpoint shadow '+str(f))
    else:
     recorded=previous['guards_after'].get(str(f),'MISSING');need(recorded!='MISSING' and recorded==v,'recorded external candidate drift '+str(f))
  if name!=ENDPOINT:
   selected=previous['selected'][name];need(selected['root']==1 and out[selected['path']] is not None and out[selected['path']]['sha256']==selected['sha256'],'old selected external drift '+name)
 return out
def check_inputs():
 for f,h in PINS.items():need(f.is_file() and SHA(f)==h,'input pin '+str(f))
 imports_valid();return direct_guard()
def available():
 for line in Path('/proc/meminfo').read_text().splitlines():
  if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
 raise RuntimeError('MemAvailable unavailable')
def stat(pid):
 fields=Path('/proc',str(pid),'stat').read_text().rsplit(')',1)[1].split();return fields[0],int(fields[3])
def lean_peers(own=None):
 peers=[]
 for proc in Path('/proc').iterdir():
  if not proc.name.isdecimal():continue
  try:
   if (proc/'comm').read_text().strip()!='lean':continue
   st,session=stat(int(proc.name))
   if st not in ('Z','X') and session!=own:peers.append(int(proc.name))
  except (FileNotFoundError,ProcessLookupError):continue
 return peers
def rss_session(session):
 total=0;members=[]
 for proc in Path('/proc').iterdir():
  if not proc.name.isdecimal():continue
  try:
   state,sid=stat(int(proc.name))
   if sid!=session or state in ('Z','X'):continue
   lines=(proc/'status').read_text().splitlines();rss=[int(x.split()[1])*1024 for x in lines if x.startswith('VmRSS:')]
   need(len(rss)==1,'missing session RSS '+proc.name);total+=rss[0];members.append(int(proc.name))
  except (FileNotFoundError,ProcessLookupError):continue
 return total,members
def selftest():
 assert_equal(['A.B'],parse_imports('import A.B\n#check True\n'),'parser positive')
 for bad in (['A.C'],[]):
  try:assert_equal(['A.B'],bad,'mismatch')
  except RuntimeError:pass
  else:raise RuntimeError('import mismatch control accepted')
 for vals in ((10*1024**3-1,0,1024**3),(11*1024**3,7*1024**3//2,1024**3),(11*1024**3,0,512*1024**2-1)):
  need(not within_limits(*vals),'resource refusal control accepted')
 need(within_limits(11*1024**3,0,1024**3),'resource positive control')
 for mode in ('missing','changed'):
  try:assert_equal({'x':1},{} if mode=='missing' else {'x':2},'guard mismatch')
  except RuntimeError:pass
  else:raise RuntimeError('guard mismatch control accepted')
 return {'status':'PASS_PURE_CONTROLS','scope':'Import/guard/resource pure controls only; no subprocess or Lean.'}
def atomic(path,value):
 tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n');os.replace(tmp,path)
def run():
 runner_hash=SHA(Path(__file__));before=check_inputs();need(not lean_peers(),'another Lean process is active');need(within_limits(available(),0,shutil.disk_usage('/tmp').free),'prelaunch resources')
 need(not os.path.lexists(OUT),'refusing existing output');OUT.mkdir();rows=[];state={'status':'RUNNING','cases':rows,'runner_sha256':runner_hash};atomic(OUT/'state.json',state)
 spec=importlib.util.spec_from_file_location('normalized106_owned',HELPER);owned=importlib.util.module_from_spec(spec);spec.loader.exec_module(owned)
 try:
  for name in ('endpoint','matrix'):
   need(check_inputs()==before and SHA(Path(__file__))==runner_hash,'pre-case inputs changed');source=SOURCES[name];metrics={'samples':0,'peak_session_rss':0,'min_available':available(),'min_free':shutil.disk_usage('/tmp').free,'pid':None,'reason':None}
   state['active_case']=name;state['active_metrics']=metrics;atomic(OUT/'state.json',state)
   def monitor(pid):
    metrics['pid']=pid;mem=available();rss,members=rss_session(pid);free=shutil.disk_usage('/tmp').free;metrics['samples']+=1;metrics['peak_session_rss']=max(metrics['peak_session_rss'],rss);metrics['min_available']=min(metrics['min_available'],mem);metrics['min_free']=min(metrics['min_free'],free)
    peers=lean_peers(pid);ok=within_limits(mem,rss,free) and not peers
    if not ok:metrics['reason']={'available':mem,'rss':rss,'free':free,'other_lean':peers}
    atomic(OUT/'state.json',state);return ok
   env=dict(os.environ,LEAN_PATH=str(BASE)+':'+str(PACKAGE),LEAN_NUM_THREADS='1')
   for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
   cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M2400','-j1','-DElab.async=false','--root='+str(HERE),str(source)]
   def on_reap(code,lifecycle):
    metrics['child_exit']=code;metrics['lifecycle']=lifecycle;atomic(OUT/'state.json',state)
   with (OUT/(name+'.log')).open('xb') as log:
    code,elapsed,lifecycle=owned.run(cmd,cwd=ROOT,env=env,stdout=log,stderr=log,timeout=120,disk_check=monitor,poll_interval=.25,grace=5,on_reap=on_reap)
   need(metrics['samples']>0,'no resource samples');need(check_inputs()==before and SHA(Path(__file__))==runner_hash,'post-case inputs changed')
   rows.append({'case':name,'command':cmd,'exit':code,'elapsed_seconds':elapsed,'lifecycle':lifecycle,'metrics':metrics,'log_sha256':SHA(OUT/(name+'.log'))});state['active_case']=None;atomic(OUT/'state.json',state)
  state['status']='DIAGNOSTICS_FINISHED';state['scope']='Exact two import clients, no project build; nonzero Lean exits and diagnostics require interpretation.';atomic(OUT/'result.json',state);atomic(OUT/'state.json',state)
  print(json.dumps({'status':state['status'],'cases':[{'case':x['case'],'exit':x['exit']} for x in rows],'result_sha256':SHA(OUT/'result.json')},sort_keys=True))
 except BaseException as exc:
  state['status']='FAILED_OR_STOPPED';state['failure']=repr(exc);atomic(OUT/'state.json',state);raise
if __name__=='__main__':
 if sys.argv[1:]==['--selftest']:print(json.dumps(selftest(),sort_keys=True))
 elif sys.argv[1:]==['--preflight']:
  guard=check_inputs();need(not lean_peers(),'another Lean process is active');need(within_limits(available(),0,shutil.disk_usage('/tmp').free),'preflight resources');print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','guard_entries':len(guard),'scope':'Direct path/companion inventory, no import or process launched.'},sort_keys=True))
 elif sys.argv[1:]==['--run']:run()
 else:raise SystemExit('choose --selftest, --preflight or --run')
