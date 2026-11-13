import hashlib,importlib.util,json,os,subprocess,sys
from pathlib import Path
m=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py');sp=importlib.util.spec_from_file_location('mon',m);mon=importlib.util.module_from_spec(sp);sp.loader.exec_module(mon)
r=Path('/tmp/ipra-sparse-k-family-01');lib=r/'lib';srcroot=r/'frozen';base=Path('/tmp/compact44-k-radix-cert-01/lib');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');lean='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean';env={'PATH':'/usr/bin:/bin','HOME':'/home/codex','LEAN_PATH':str(lib)+':'+str(base)+':'+str(pkg)};H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['ConcreteSparseKernel']:
 src=srcroot/(name+'.lean');obj=lib/(name+'.olean');log=r/(name+'.log');dp=subprocess.run([lean,'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120);(r/(name+'.deps')).write_text(dp.stdout);(r/(name+'.deps.stderr')).write_text(dp.stderr)
 if dp.returncode!=0 or dp.stderr:raise ValueError(('deps',name,dp.returncode,dp.stderr))
 cmd=[lean,'-M3000','-j1','-DElab.async=false','--root='+str(srcroot),str(src),'-o',str(obj)];code,peak,reason=mon.monitored(cmd,env,log,timeout=300);print(json.dumps({'module':name,'command':cmd,'deps_exit':dp.returncode,'compiler_exit':code,'peak_sampled_rss_bytes':peak,'reason':reason,'source_sha256':H(src),'log_sha256':H(log)}),flush=True)
 if code!=0 or reason is not None or 'warning:' in log.read_text() or 'sorryAx' in log.read_text():sys.exit(1)
