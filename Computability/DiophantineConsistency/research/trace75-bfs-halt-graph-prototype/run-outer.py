#!/usr/bin/env python3
from pathlib import Path
from hashlib import sha256
import argparse,json,os,subprocess,sys,time
H=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--attempt',required=True);a=p.parse_args().attempt
if a!='attempt03':raise SystemExit('only reviewed attempt03')
r=H/'run-v3.py';policy=H/'observations/policy-attempt01/result.json';source=H/'Trace75BFSHaltGraph.lean'
pins={r:'5d32b766ba402d9ed2c926fda5ec7f0e78a93bfea8854b90b517a63532222909',policy:'2952f35d52ec93354938bc820e47fea8c905621b186d3d869e88d16f90ca812e',source:'9ad0f1b7a90c8305d95978024881382a6b88e9c3794cdc7c1447c4220a29957d'}
def sha(p):return sha256(p.read_bytes()).hexdigest()
def check():return {str(p):sha(p) for p in pins}
if check()!={str(p):v for p,v in pins.items()}:raise SystemExit('input pin mismatch')
obs=H/'observations'/('outer-'+a);child=H/'observations'/('directbfshalt80-'+a)
if obs.exists() or child.exists():raise SystemExit('attempt exists')
obs.mkdir();before=check();wrapper_before=sha(Path(__file__));start=time.monotonic()
cmd=[sys.executable,'-I','-S','-B',str(r)];env={'PATH':'/usr/bin:/bin','ATTEMPT':a}
with (obs/'stdout').open('xb') as out,(obs/'stderr').open('xb') as err:
 proc=subprocess.run(cmd,stdout=out,stderr=err,env=env)
after=check();wrapper_after=sha(Path(__file__));terminal=child/'terminal.json'
result={'command':cmd,'env':env,'child_exit':proc.returncode,'elapsed':time.monotonic()-start,'inputs_before':before,'inputs_after':after,'wrapper_before':wrapper_before,'wrapper_after':wrapper_after,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),'terminal_sha256':sha(terminal) if terminal.is_file() else None}
tmp=obs/'result.tmp';tmp.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');os.replace(tmp,obs/'result.json')
print(json.dumps({'child_exit':proc.returncode,'terminal_sha256':result['terminal_sha256'],'inputs_stable':before==after,'wrapper_stable':wrapper_before==wrapper_after}))
if proc.returncode or before!=after or wrapper_before!=wrapper_after or not terminal.is_file():raise SystemExit(1)
