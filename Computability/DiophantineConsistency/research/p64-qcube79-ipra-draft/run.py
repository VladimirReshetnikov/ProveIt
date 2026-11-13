#!/usr/bin/env python3
"""Bounded 79-endpoint client check with pinned direct inputs."""
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
OUT = Path('/tmp/p64-qcube79-ipra-check01')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
GUARDS = {
    str(HERE/'P64QCube79Endpoint.lean'): '982c587f1eb8e801de36efa1ef33b1a1b4dec235c203dd028571574951b24fb0',
    '/tmp/P64QCube79Existence.olean': 'bd6c23e7857eb62216def8e113082c1ef8e7b6ec695f044e5cd2b2c17a29872f',
    '/tmp/p64-qcube80-ipra-check01/P64QCube80Endpoint.olean': '2486d2b671dce6751c656830dde439bda0c0de3dcbca2a82842c8dd1331f3c6c',
    '/tmp/P64QCube79.olean': '9f9c2112fa677ac6b330bc722741386da048fd9e01d091aa09dcdb60d24def65',
    str(LEAN): 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def guard():
    for path, expected in GUARDS.items():
        if sha(path)!=expected:
            raise RuntimeError('guard mismatch: '+path)


if OUT.exists():
    raise SystemExit('refusing existing output directory')
processes=subprocess.run(['ps','-eo','pid=,stat=,comm='],check=True,text=True,stdout=subprocess.PIPE).stdout
if any(len(parts)==3 and parts[2]=='lean' and not parts[1].startswith('Z')
       for parts in (line.split() for line in processes.splitlines())):
    raise SystemExit('Lean slot is not free')
guard()
OUT.mkdir()
env=os.environ.copy()
env['LEAN_PATH']='/tmp/p64-qcube80-ipra-check01:/tmp/p64-qcube81-ipra-check01:/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
obj=OUT/'P64QCube79Endpoint.olean'
cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false','--root='+str(HERE),str(HERE/'P64QCube79Endpoint.lean'),'-o',str(obj)]
start=time.monotonic()
try:
    result=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    log,code=result.stdout,result.returncode
except subprocess.TimeoutExpired as exc:
    log=(exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout,bytes) else (exc.stdout or '')
    log+='\nTimed out after 300 seconds.\n';code=124
(OUT/'compile.log').write_text(log)
guard()
record={'exit':code,'seconds':round(time.monotonic()-start,3),'command':cmd,'lean_path':env['LEAN_PATH'],
        'guards_before_after':GUARDS,'log_sha256':sha(OUT/'compile.log'),
        'object_sha256':sha(obj) if obj.exists() else None,
        'scope':'guarded direct inputs; inherited full project/package/dynamic/search-path ancestry'}
(OUT/'result.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(log,end='')
names=('positiveBridge','native_equivalence','standard_equivalence','reference_equivalence')
expected=[f"'P64QCube79Endpoint.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names]
if code or any(x in log for x in ('sorryAx','error:','warning:')) or any(x not in log for x in expected):
    raise SystemExit(1)
print('PASS: guarded 79-operation endpoint client')
