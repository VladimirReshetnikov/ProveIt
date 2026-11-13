#!/usr/bin/env python3
"""Exercise initialization/guard controls only; never execute a Lean stage."""
import fcntl
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
HERE=Path(__file__).resolve().parent
RUNNER=HERE/'replay.py'
CURRENT=Path('/tmp/nine-ipra-guarded-author-20261102-e')
OLD=Path('/tmp/nine-ipra-guarded-author-20261102-d')
def run(flags,output,option):
    cmd=[sys.executable,*flags,'-I','-S','-B',str(RUNNER),'--output',str(output),option]
    p=subprocess.run(cmd,capture_output=True,text=True,timeout=120,check=False)
    return {'command':cmd,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
good=run([],CURRENT,'--check')
drift=run([],OLD,'--check')
duplicate=run([],CURRENT,'--init')
optimized=run(['-O'],CURRENT,'--check')
with (CURRENT/'.lock').open('a') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    locked=run([],CURRENT,'--check')
if not (good['exit_code']==0 and 'READY_NO_LEAN 0 completed' in good['stdout'] and
        drift['exit_code']==1 and 'manifest or runner drift' in drift['stderr'] and
        duplicate['exit_code']==1 and 'output already exists' in duplicate['stderr'] and
        optimized['exit_code']==1 and 'without optimization' in optimized['stderr'] and
        locked['exit_code']==1 and ('Resource temporarily unavailable' in locked['stderr'] or
                                     'BlockingIOError' in locked['stderr'])):
    raise RuntimeError(json.dumps([good,drift,duplicate,optimized,locked],indent=2))
manifest=CURRENT/'manifest.json'
print(json.dumps({'status':'PASS_NO_LEAN_RUNNER_CONTROLS',
                  'runner_sha256':sha256(RUNNER.read_bytes()).hexdigest(),
                  'manifest_sha256':sha256(manifest.read_bytes()).hexdigest(),
                  'checks':[good,drift,duplicate,optimized,locked],
                  'scope':'initialization, drift, duplicate, optimization and lock controls only; no Lean stage'},
                 indent=2,sort_keys=True))
