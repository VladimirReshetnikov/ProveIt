#!/usr/bin/env python3
"""Capture the guarded endpoint runner's actual outer process exit."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys,time
H=Path(__file__).resolve().parent;runner=H/'run.py';obs=H/'observations/outer-attempt01'
if obs.exists():raise SystemExit('refusing to overwrite outer receipt')
def sh(p):return sha256(Path(p).read_bytes()).hexdigest()
pin='2d67b7118319bb22b7471de6f4f9ca10aad3fd8ea4a4f4922408feb73f49b93b'
if sh(runner)!=pin:raise SystemExit('runner pin mismatch')
obs.mkdir(parents=True);cmd=[sys.executable,str(runner)];start=time.monotonic()
with (obs/'stdout').open('xb') as out,(obs/'stderr').open('xb') as err:
 proc=subprocess.run(cmd,stdout=out,stderr=err,check=False)
d={'command':cmd,'exit':proc.returncode,'elapsed':time.monotonic()-start,'runner_sha256':sh(runner),'wrapper_sha256':sh(__file__),'stdout_sha256':sh(obs/'stdout'),'stderr_sha256':sh(obs/'stderr')}
(obs/'terminal.json').write_text(json.dumps(d,indent=2,sort_keys=True)+'\n');print(json.dumps(d),flush=True)
if proc.returncode!=0:raise SystemExit(1)
