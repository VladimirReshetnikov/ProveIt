#!/usr/bin/env python3
"""Temporary fake-repo worker authorization test. Never starts Lean."""
import json
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('run with python3 -I -S -B')
ROOT=Path(__file__).resolve().parents[2]
PREP=Path(__file__).resolve().parent/'snapshot'
manifest=PREP.parent/'snapshot-hashes.json'
if hashlib.sha256(manifest.read_bytes()).hexdigest()!='ca82c9ef14c7853da7a90179daf9778e7fc6b9ad382e007483ef397b15b14a51':
    raise RuntimeError('reviewed v3 hash manifest drift')
for name,digest in json.loads(manifest.read_text()).items():
    if hashlib.sha256((PREP/name).read_bytes()).hexdigest()!=digest:
        raise RuntimeError('reviewed v3 control snapshot drift: '+name)
pins={'launch.py':'3e613f3a8985ab64a2b3c4cad4e6b8eeff261726e9c7007ea4adda388c146a14',
 'worker.py':'b5c31eebd66e9edf3d6f8fb47f6e7bf8b2c957509e78ade91119340f8a19730c',
 'traversal_core.py':'e1c4062ed3e392c57c1a62ff7b1548edcb80688c0e103bd226f4dac249c568d9',
 'supervision.py':'6ecb9d3ef4770b373c7646424afecc212493987282e090c93bbd500942b2f0af'}
for name,digest in pins.items():
    if hashlib.sha256((PREP/name).read_bytes()).hexdigest()!=digest:
        raise RuntimeError('reviewed v3 snapshot drift: '+name)
for tool in ('ionice','nice'):
    if shutil.which(tool) is None: raise RuntimeError('missing tool '+tool)
driver=r'''import hashlib,json,os,subprocess,sys
from pathlib import Path
h=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=[h/n for n in ('worker.py','traversal_core.py','supervision.py','launch.py')]
gate=h/'review-gate.json'
gate.write_text(json.dumps({'decision':'PASS_PRELAUNCH_REVIEW','reviewer':'synthetic-fake-repo',
 'code_hashes':{str(p):sha(p) for p in files}}))
r,w=os.pipe();os.write(w,(str(os.getpid())+':'+sha(gate)).encode());os.close(w)
env=dict(os.environ,HEADER_WORKER_AUTH_FD=str(r))
p=subprocess.run(['ionice','-c','3','nice','-n','19',sys.executable,'-I','-S','-B',str(h/'worker.py')],
 env=env,pass_fds=(r,),start_new_session=True,capture_output=True,text=True,timeout=10)
os.close(r)
if p.returncode==0:raise RuntimeError('worker unexpectedly succeeded')
if 'pinned input mismatch' in p.stderr and 'inventory.py' in p.stderr: result='authenticated_then_rejected_bad_inventory'
elif 'worker lacks reviewed supervisor session' in p.stderr: result='supervisor_session_rejected'
else: raise RuntimeError(p.stdout+'\n'+p.stderr)
print(result)
'''
with tempfile.TemporaryDirectory(prefix='header-v2-handshake-audit-') as t:
    fake=Path(t);(fake/'lakefile.toml').write_text('')
    research=fake/'Computability/DiophantineConsistency/research';dest=research/'stub';dest.mkdir(parents=True)
    for f in ('worker.py','traversal_core.py','supervision.py'):shutil.copyfile(PREP/f,dest/f)
    (dest/'launch.py').write_text(driver)
    marker=fake/'inventory-executed'
    inventory=research/'compiled-header-inventory/inventory.py';inventory.parent.mkdir()
    inventory.write_text('from pathlib import Path\nPath('+repr(str(marker))+').write_text("BAD")\n')
    for path in ('nine-variable-external-matrix-preflight/header-result.json',
                 'nine-variable-current-base-source-survey/result-final.json',
                 'nine-variable-external-matrix-preflight/policy.json'):
        dst=research/path;dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(ROOT/'research'/path,dst)
    env=dict(os.environ);env.pop('HEADER_WORKER_AUTH_FD',None)
    args=[sys.executable,'-I','-S','-B']
    absolute=subprocess.run(args+[str(dest/'launch.py')],cwd=dest,env=env,capture_output=True,text=True,timeout=15,check=True)
    relative=subprocess.run(args+['launch.py'],cwd=dest,env=env,capture_output=True,text=True,timeout=15,check=True)
    assert absolute.stdout.strip()=='authenticated_then_rejected_bad_inventory',absolute.stdout+absolute.stderr
    assert relative.stdout.strip()=='authenticated_then_rejected_bad_inventory',relative.stdout+relative.stderr
    assert not marker.exists(),'mismatched synthetic inventory executed'
print(json.dumps({'status':'PASS_SYNTHETIC_HANDSHAKES','wrapped_absolute_handshake':'PASS',
 'wrapped_relative_handshake':'PASS','fake_inventory_executed':False,
 'scope':'Temporary fake repository and fake gate; no real gate, Lean, or header traversal.'},sort_keys=True))
