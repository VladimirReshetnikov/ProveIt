#!/usr/bin/env python3
"""Capture the actual outer aggregate-runner exit without overwriting evidence."""
from pathlib import Path
from hashlib import sha256
import json, os, subprocess, sys
H=Path(__file__).resolve().parent
obs=H/'observations'/'outer-attempt01'
if obs.exists():raise SystemExit('outer attempt exists')
runner=H/'run-v2.py'
def digest(p):return sha256(p.read_bytes()).hexdigest()
if digest(runner)!='a380ac8a2caabfabe093557631d1f7b6e94d1217f4869c80ceb6b58453dd1a3b':raise SystemExit('runner pin changed')
obs.mkdir(parents=True)
cmd=[sys.executable,str(runner)]
with (obs/'stdout').open('x') as out,(obs/'stderr').open('x') as err:
 p=subprocess.run(cmd,stdout=out,stderr=err,env={**os.environ,'ATTEMPT':'attempt01'})
record={'command':cmd,'runner_sha256':digest(runner),'wrapper_sha256':digest(Path(__file__)),'exit':p.returncode,'stdout_sha256':digest(obs/'stdout'),'stderr_sha256':digest(obs/'stderr')}
(obs/'terminal.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps(record),flush=True)
sys.exit(p.returncode)
