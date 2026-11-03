#!/usr/bin/env python3
"""Launch the released v6 attempt once and capture the outer process exit."""
from hashlib import sha256
from pathlib import Path
import json, subprocess, sys, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('use python3 -I -S -B without optimization')
H=Path(__file__).resolve().parent;RUNNER=H/'run-v6.py';O=H/'observations/outer-attempt04'
expected='1956a0831c4dc93c5f30ff578ec6e7731c7d56f4be695d3ee8a7c4681a982298'
digest=lambda p:sha256(Path(p).read_bytes()).hexdigest()
if digest(RUNNER)!=expected:raise SystemExit('runner changed')
if O.exists() or (H/'observations/attempt04').exists():raise SystemExit('attempt exists')
O.mkdir(parents=True)
cmd=[sys.executable,'-I','-S','-B',str(RUNNER),'--attempt','attempt04']
start=time.monotonic()
with (O/'stdout').open('x') as so,(O/'stderr').open('x') as se:
 p=subprocess.run(cmd,stdout=so,stderr=se)
result={'command':cmd,'exit':p.returncode,'elapsed':time.monotonic()-start,
        'runner_sha256_before':expected,'runner_sha256_after':digest(RUNNER),
        'stdout_sha256':digest(O/'stdout'),'stderr_sha256':digest(O/'stderr')}
(O/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True),flush=True)
sys.exit(p.returncode)
