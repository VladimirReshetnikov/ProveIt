#!/usr/bin/env python3
"""Bounded 77-endpoint client check with pinned direct inputs."""
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
OUT = Path('/tmp/p64-qcube77-ipra-check01')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
GUARDS = {
    str(HERE/'P64QCube77Endpoint.lean'): '921fbdf5f333959f6a7abf43cf7853df0512683c26de342f025bc4c700ea9154',
    '/tmp/P64QCube77Existence.olean': '0cd0fa8b52a8cad49bad9db49507f16acb0171ee56dad0e21783515facf15a72',
    '/tmp/p64-qcube78-ipra-check01/P64QCube78Endpoint.olean': 'a2e7bb5d0303e42afeb0f59331ca740f8397a3c681aa815d7559f15e7fb82eea',
    '/tmp/P64QCube77.olean': 'daa0b689982287a74991a14c588a23d64f7bc1b5959a2528d000a6f64c0bc99d',
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
env['LEAN_PATH']='/tmp/p64-qcube78-ipra-check01:/tmp/p64-qcube79-ipra-check01:/tmp/p64-qcube80-ipra-check01:/tmp/p64-qcube81-ipra-check01:/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
obj=OUT/'P64QCube77Endpoint.olean'
cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false','--root='+str(HERE),str(HERE/'P64QCube77Endpoint.lean'),'-o',str(obj)]
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
expected=[f"'P64QCube77Endpoint.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names]
if code or any(x in log for x in ('sorryAx','error:','warning:')) or any(x not in log for x in expected):
    raise SystemExit(1)
print('PASS: guarded 77-operation endpoint client')
