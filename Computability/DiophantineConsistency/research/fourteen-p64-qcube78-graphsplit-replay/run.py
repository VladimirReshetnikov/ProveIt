#!/usr/bin/env python3
"""Replay the actual-zero 78 split with pinned direct objects and a receipt."""
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent/'fourteen-p64-qcube78-split-draft/P64QCube78GraphSplit.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OUT = Path('/tmp/p64-qcube78-graphsplit-independent-check01')
OBS = HERE/'observations/attempt01'
PATHS = ['/tmp/p64-qcube81-ipra-check01', '/tmp/p64-independent-captured-replay/lib', '/tmp',
         '/tmp/trace74-direct-four-block-1zltaw2f/lib', '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']
GUARDS = {
    str(SOURCE): 'f0bb74cf05302f5067a0f99fbb4f5b8f63e9cb75ad11154bc82b0219004c5020',
    '/tmp/P64QCube78.olean': '112e4979a76e241719cbb1b682e98c8cebabb3150c3349055dd6964ed12be0f5',
    '/tmp/P64QCube78Split.olean': 'ccdfdcbee3c4de43f2bb3924fcbdeade0eb2b7e0cc9a99e1d64bf07e52ddced9',
    str(LEAN): 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
}
EXPECTED_OBJECT = '76da5f69b14d211994c5ccc12e9e9de9d5d3b585b002149bca4922d7ca536150'
def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def guard():
    actual={path:sha(path) for path in GUARDS}
    if actual != GUARDS: raise RuntimeError('direct-input hash mismatch')
    for name in ('P64QCube78','P64QCube78Split'):
        resolved=next((Path(root)/(name+'.olean') for root in PATHS if (Path(root)/(name+'.olean')).is_file()),None)
        if resolved != Path('/tmp')/(name+'.olean'): raise RuntimeError('unexpected direct-import resolution: '+repr(resolved))
    return actual
if OUT.exists() or OBS.exists(): raise SystemExit('refusing existing output or observation')
ps=subprocess.run(['ps','-eo','pid=,stat=,comm='],check=True,text=True,stdout=subprocess.PIPE).stdout
if any(len(a)==3 and a[2]=='lean' and not a[1].startswith('Z') for a in (x.split() for x in ps.splitlines())):
    raise SystemExit('Lean slot is not free')
before=guard()
OUT.mkdir();OBS.mkdir(parents=True)
env=os.environ.copy();env['LEAN_PATH']=':'.join(PATHS)
obj=OUT/'P64QCube78GraphSplit.olean'
cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false','--root='+str(SOURCE.parent),str(SOURCE),'-o',str(obj)]
start=time.monotonic()
try:
    r=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    log,code=r.stdout,r.returncode
except subprocess.TimeoutExpired as exc:
    log=(exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout,bytes) else (exc.stdout or '')
    log+='\nTimed out after 300 seconds.\n';code=124
(OBS/'compile.log').write_text(log)
try: after,guard_error=guard(),None
except Exception as exc: after,guard_error=None,repr(exc)
expected="'P64QCube78GraphSplit.first_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
rec={'exit':code,'elapsed_seconds':round(time.monotonic()-start,3),'command':cmd,'lean_path':env['LEAN_PATH'],
     'guards_before':before,'guards_after':after,'guard_error':guard_error,
     'log_sha256':sha(OBS/'compile.log'),'output_sha256':sha(obj) if obj.is_file() else None,
     'expected_output_hash':EXPECTED_OBJECT,'exact_log':log==expected,'runner_sha256':sha(__file__),
     'scope':'single same-provider replay; direct inputs and first existing import paths guarded; full transitive project/package/dynamic ancestry inherited'}
(OBS/'result.json').write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
print(log,end='')
if code!=0 or guard_error or log!=expected or not obj.is_file() or sha(obj)!=EXPECTED_OBJECT:
    raise SystemExit('FAIL: see retained observation')
print('PASS: independent 78 actual-zero split replay')
