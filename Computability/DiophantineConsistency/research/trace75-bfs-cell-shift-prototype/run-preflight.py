#!/usr/bin/env python3
"""Capture the read-only fresh-union support preflight."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;RUN=H/'run.py';O=H/'observations/preflight-attempt01';PIN='019aed0d7e29601dfd3728dbe329fb26f0030a006b0fa0620d1e2017aaa17095'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
if O.exists() or sha(RUN)!=PIN:raise SystemExit('output exists or runner drift')
O.mkdir(parents=True);cmd=[sys.executable,'-I','-S','-B',str(RUN),'--preflight-only']
with (O/'stdout').open('x') as out,(O/'stderr').open('x') as err:r=subprocess.run(cmd,stdout=out,stderr=err,env={'PATH':'/usr/bin:/bin'})
x={'command':cmd,'exit':r.returncode,'runner_sha256_before':PIN,'runner_sha256_after':sha(RUN),'wrapper_sha256':sha(__file__),'stdout_sha256':sha(O/'stdout'),'stderr_sha256':sha(O/'stderr'),'scope':'read-only fresh-union preflight; no Lean'}
(O/'terminal.json').write_text(json.dumps(x,indent=2,sort_keys=True)+'\n');print(json.dumps(x))
if r.returncode or x['runner_sha256_after']!=PIN:raise SystemExit(1)
