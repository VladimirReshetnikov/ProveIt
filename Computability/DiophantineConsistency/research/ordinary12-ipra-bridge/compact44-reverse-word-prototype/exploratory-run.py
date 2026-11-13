import hashlib,importlib.util,json,os,re,sys
from pathlib import Path
root=Path('/tmp/compact-reverse-explore-01');srcroot=root/'src';lib=root/'lib';out=[]
monitorpath=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py')
spec=importlib.util.spec_from_file_location('mon',monitorpath);mon=importlib.util.module_from_spec(spec);spec.loader.exec_module(mon)
lean='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
env=os.environ.copy()
for k in tuple(env):
 if k.startswith('PYTHON') or k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(k,None)
env['LEAN_PATH']=str(lib)+':/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
for n in ['CompactInverseInventory','CompactForbidden','CompactNoExtra','CompactMarkedReverse','CompactCyclicBridge']:
 src=srcroot/'DiophantineConsistency'/(n+'.lean');obj=lib/'DiophantineConsistency'/(n+'.olean');log=root/(n+'.log')
 if os.path.lexists(obj):raise ValueError(('collision',str(obj)))
 cmd=[lean,'-M4000','-j1','-DElab.async=false',f'--root={srcroot}',str(src),'-o',str(obj)]
 code,peak,reason=mon.monitored(cmd,env,log,timeout=600);text=log.read_text()
 row={'module':n,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'exit':code,'stop_reason':reason,'sampled_peak_rss_bytes':peak,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()};out.append(row)
 (root/'progress.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(row),flush=True)
 if code or reason or not obj.is_file() or re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text):
  print(text[-6000:],flush=True);sys.exit(1)
print('EXPLORATORY_CHAIN_PASSED',flush=True)
