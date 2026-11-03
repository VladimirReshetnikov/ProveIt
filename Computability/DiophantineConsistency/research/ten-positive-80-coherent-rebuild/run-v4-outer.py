#!/usr/bin/env python3
"""Launch the released v4 attempt once and capture the outer process exit."""
from hashlib import sha256
from pathlib import Path
import json, subprocess, sys, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('use python3 -I -S -B without optimization')
H=Path(__file__).resolve().parent;RUNNER=H/'run-v4.py';O=H/'observations/outer-attempt02'
expected='6065f48448b7956355ad277e481047ec88cfea7ba09d9de99fb6542513398ca9'
digest=lambda p:sha256(Path(p).read_bytes()).hexdigest()
if digest(RUNNER)!=expected:raise SystemExit('runner changed')
if O.exists() or (H/'observations/attempt02').exists():raise SystemExit('attempt exists')
O.mkdir(parents=True)
cmd=[sys.executable,'-I','-S','-B',str(RUNNER),'--attempt','attempt02']
start=time.monotonic()
with (O/'stdout').open('x') as so,(O/'stderr').open('x') as se:
 p=subprocess.run(cmd,stdout=so,stderr=se)
result={'command':cmd,'exit':p.returncode,'elapsed':time.monotonic()-start,
        'runner_sha256_before':expected,'runner_sha256_after':digest(RUNNER),
        'stdout_sha256':digest(O/'stdout'),'stderr_sha256':digest(O/'stderr')}
(O/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True),flush=True)
sys.exit(p.returncode)
