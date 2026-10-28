"""Preserve every finite audit attempt; no compiler/dependency invocation."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
mode=sys.argv[1] if len(sys.argv)==2 else ''
if mode not in ('write','normal','optimized'):
    raise SystemExit('usage: run.py write|normal|optimized')
if shutil.disk_usage(HERE).free<512*1024**2:
    raise RuntimeError('512MiB reserve')
attempts=HERE/'attempts'; attempts.mkdir(exist_ok=True)
index=1
while (attempts/str(index)).exists(): index+=1
out=attempts/str(index); out.mkdir()


def pin(p):
    raw=p.read_bytes()
    return {'path':str(p),'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}


sources=[]
for name in ('audit.py','run.py','PROOF.md','polynomial.json','INPUTS.json'):
    p=HERE/name; sources.append(pin(p)); shutil.copyfile(p,out/name)
command=[sys.executable,'-B']+(['-O'] if mode=='optimized' else [])+[str(HERE/'audit.py')]+(['--write'] if mode=='write' else [])
state={'mode':mode,'command':command,'status':'RUNNING','sources':sources,'python':pin(Path(sys.executable).resolve())}
path=out/'state.json'
path.write_text(json.dumps(state,indent=2)+'\n')
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0')
start=time.monotonic()
with (out/'stdout.log').open('w') as log:
    result=subprocess.run(['/usr/bin/time','-v','-o',str(out/'timing.log'),*command],env=env,stdout=log,stderr=subprocess.STDOUT)
state.update(exit_code=result.returncode,seconds=time.monotonic()-start,
             stdout=pin(out/'stdout.log'),timing=pin(out/'timing.log'),free_bytes=shutil.disk_usage(HERE).free)
same=all(pin(Path(p['path']))==p for p in sources)
state['sources_unchanged']=same
state['status']='PASS' if result.returncode==0 and same and state['free_bytes']>=512*1024**2 else 'FAILED'
if (HERE/'CERTIFICATE.json').exists():
    state['certificate']=pin(HERE/'CERTIFICATE.json')
path.write_text(json.dumps(state,indent=2)+'\n')
print(json.dumps({'attempt':index,'status':state['status'],'seconds':state['seconds'],'state':pin(path)},indent=2))
print((out/'stdout.log').read_text(),end='')
if state['status']!='PASS': raise SystemExit(1)
