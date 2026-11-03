#!/usr/bin/env python3
"""Run the approved selected-ancestry scan once and record its actual exit."""
from pathlib import Path
from hashlib import sha256
import json,os,subprocess,sys,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;RUN=H/'scan-v2.py';O=H/'observations/outer-attempt01';PIN='c8e55712c29c8fb60de059c6451ffc5a4aa93319c3cfe20c70952837b4e1e2e2'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
if O.exists() or (H/'observations/scan-attempt01').exists():raise SystemExit('attempt exists')
if sha(RUN)!=PIN:raise SystemExit('scanner hash mismatch')
O.mkdir(parents=True);cmd=[sys.executable,'-I','-S','-B',str(RUN)];start=time.time_ns()
with (O/'stdout').open('x') as out,(O/'stderr').open('x') as err:
 proc=subprocess.Popen(cmd,stdout=out,stderr=err,env={'PATH':'/usr/bin:/bin'})
 (O/'pid').write_text(str(proc.pid)+'\n');code=proc.wait()
r={'command':cmd,'exit':code,'start_ns':start,'end_ns':time.time_ns(),'scanner_sha256_before':PIN,'scanner_sha256_after':sha(RUN),'wrapper_sha256':sha(__file__),'stdout_sha256':sha(O/'stdout'),'stderr_sha256':sha(O/'stderr')}
tmp=O/'terminal.tmp';tmp.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');os.replace(tmp,O/'terminal.json')
print(json.dumps({'exit':code,'scanner_stable':r['scanner_sha256_after']==PIN,'terminal_sha256':sha(O/'terminal.json')}))
if code!=0 or r['scanner_sha256_after']!=PIN:raise SystemExit(1)
