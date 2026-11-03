#!/usr/bin/env python3
"""Launch the released v5 attempt once and capture the outer process exit."""
from hashlib import sha256
from pathlib import Path
import json, subprocess, sys, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('use python3 -I -S -B without optimization')
H=Path(__file__).resolve().parent;RUNNER=H/'run-v5.py';O=H/'observations/outer-attempt03'
expected='67f287a75d095fc45abde2d14acc732110956e3e248c154e817f92b14eb43558'
digest=lambda p:sha256(Path(p).read_bytes()).hexdigest()
if digest(RUNNER)!=expected:raise SystemExit('runner changed')
if O.exists() or (H/'observations/attempt03').exists():raise SystemExit('attempt exists')
O.mkdir(parents=True)
cmd=[sys.executable,'-I','-S','-B',str(RUNNER),'--attempt','attempt03']
start=time.monotonic()
with (O/'stdout').open('x') as so,(O/'stderr').open('x') as se:
 p=subprocess.run(cmd,stdout=so,stderr=se)
result={'command':cmd,'exit':p.returncode,'elapsed':time.monotonic()-start,
        'runner_sha256_before':expected,'runner_sha256_after':digest(RUNNER),
        'stdout_sha256':digest(O/'stdout'),'stderr_sha256':digest(O/'stderr')}
(O/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True),flush=True)
sys.exit(p.returncode)
