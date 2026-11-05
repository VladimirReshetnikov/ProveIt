#!/usr/bin/env python3
"""Isolated stub regressions: no Lean or real inventory execution."""
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
repo=next(p for p in here.parents if (p/'lakefile.toml').is_file())
with tempfile.TemporaryDirectory(prefix='header-gate-controls-') as tmp:
    fake=Path(tmp);(fake/'lakefile.toml').write_text('')
    research=fake/'Computability/DiophantineConsistency/research';dest=research/'stub';dest.mkdir(parents=True)
    for name in ('worker.py','traversal_core.py','supervision.py'):
        shutil.copyfile(here/name,dest/name)
    marker=fake/'inventory-executed'
    inventory=research/'compiled-header-inventory/inventory.py';inventory.parent.mkdir()
    inventory.write_text('from pathlib import Path\nPath('+repr(str(marker))+').write_text("BAD")\n')
    for name in ('nine-variable-external-matrix-preflight/header-result.json',
                 'nine-variable-current-base-source-survey/result-final.json',
                 'nine-variable-external-matrix-preflight/policy.json'):
        target=research/name;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(repo/'Computability/DiophantineConsistency/research'/name,target)
    env=dict(os.environ);env.pop('HEADER_WORKER_AUTH_FD',None)
    direct=subprocess.run([sys.executable,'-I','-S','-B',str(dest/'worker.py')],capture_output=True,text=True,env=env)
    if direct.returncode==0 or 'missing supervisor authorization pipe' not in direct.stderr or marker.exists():
        raise RuntimeError('direct worker bypass or helper side effect')
    # Synthetic launch file supplies a reviewed gate and the inherited session pipe.
    # The fake inventory has deliberately mismatching bytes and would create marker
    # at top level if executed. No real launcher, worker, or Lean traversal is run.
    driver='''import hashlib,json,os,subprocess,sys
from pathlib import Path
h=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=[h/n for n in ('worker.py','traversal_core.py','supervision.py','launch.py')]
gate=h/'review-gate.json'
gate.write_text(json.dumps({'decision':'PASS_PRELAUNCH_REVIEW','reviewer':'synthetic','code_hashes':{str(p):sha(p) for p in files}}))
r,w=os.pipe();os.write(w,(str(os.getpid())+':'+sha(gate)).encode());os.close(w)
env=dict(os.environ,HEADER_WORKER_AUTH_FD=str(r))
p=subprocess.run(['ionice','-c','3','nice','-n','19',sys.executable,'-I','-S','-B',str(h/'worker.py')],env=env,pass_fds=(r,),start_new_session=True,capture_output=True,text=True,timeout=10)
os.close(r)
if p.returncode==0 or 'pinned input mismatch' not in p.stderr or 'inventory.py' not in p.stderr:
 print(p.stdout,p.stderr);sys.exit(1)
'''
    (dest/'launch.py').write_text(driver)
    for mode,launcher in (('absolute',str(dest/'launch.py')),('relative','launch.py')):
        checked=subprocess.run([sys.executable,'-I','-S','-B',launcher],cwd=dest,
                               capture_output=True,text=True,env=env,timeout=15)
        if checked.returncode or marker.exists():
            raise RuntimeError(mode+' launcher rejected or mismatched helper executed: '+checked.stdout+checked.stderr)
print(json.dumps({'status':'PASS_SYNTHETIC_WORKER_GATE_CONTROLS','direct_worker_rejected':True,
                  'mismatched_inventory_rejected_before_execution':True,
                  'wrapped_absolute_and_relative_launcher_accepted':True,
                  'scope':'Temporary synthetic stub only; no real inventory or Lean traversal.'},sort_keys=True))
