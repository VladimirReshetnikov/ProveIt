#!/usr/bin/env python3
"""DRAFT: preserve outer process result; do not launch before review."""
from pathlib import Path
from hashlib import sha256
import argparse, json, os, re, subprocess, sys, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
H=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--attempt',required=True);a=p.parse_args()
if re.fullmatch(r'attempt[0-9]{2,}',a.attempt) is None:raise SystemExit('bad attempt')
obs=H/'observations'/('outer-'+a.attempt);obs.mkdir(parents=True,exist_ok=False)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
runner=H/'run-v2.py';self=Path(__file__);expected_runner='b19034d2e356e4656ba3f7efdec8c2a1b841152a834aea521f7f7d8b1f5663e7'
pins={'runner':sha(runner),'outer':sha(self)}
if pins['runner']!=expected_runner:raise SystemExit('reviewed runner SHA mismatch before launch')
cmd=[sys.executable,'-I','-S','-B',str(runner),'--attempt',a.attempt];start=time.monotonic()
with (obs/'stdout').open('xb') as so,(obs/'stderr').open('xb') as se:
    proc=subprocess.run(cmd,stdout=so,stderr=se,env={'PATH':'/usr/bin:/bin'})
after={'runner':sha(runner),'outer':sha(self)};inner=H/'observations'/a.attempt/'result.json'
inner_hash=sha(inner) if inner.is_file() else None
inner_status=json.loads(inner.read_text()).get('status') if inner.is_file() else None
result={'command':cmd,'exit':proc.returncode,'elapsed':time.monotonic()-start,'pins':pins,'after':after,
 'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),'inner_result':str(inner),
 'inner_sha256':inner_hash,'inner_status':inner_status}
(obs/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result),flush=True)
if proc.returncode!=0 or pins!=after or after['runner']!=expected_runner or inner_status!='PASS':raise SystemExit(1)
