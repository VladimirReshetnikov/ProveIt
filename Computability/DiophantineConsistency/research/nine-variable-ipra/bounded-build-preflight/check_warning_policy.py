#!/usr/bin/env python3
"""Exercise registered-warning controls on private scratch overlays, without Lean."""
import fcntl
from hashlib import sha256
from pathlib import Path
import json
import runpy
import subprocess
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
HERE=Path(__file__).resolve().parent
RUNNER=HERE/'replay.py'
FINAL=Path('/tmp/nine-ipra-guarded-author-20261102-h')
SCRATCH=Path('/tmp/nine-ipra-guarded-author-20261102-i')
OLD=Path('/tmp/nine-ipra-guarded-author-20261102-e')
EVIDENCE=OLD/'attempts/002-001'
def run(flags,out,*args):
    cmd=[sys.executable,*flags,'-I','-S','-B',str(RUNNER),'--output',str(out),*map(str,args)]
    p=subprocess.run(cmd,capture_output=True,text=True,timeout=120,check=False)
    return {'command':cmd,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
def need(ok,msg):
    if not ok: raise RuntimeError(msg)

good=run([],FINAL,'--check')
drift=run([],OLD,'--check')
duplicate=run([],FINAL,'--register-warning',EVIDENCE)
optimized=run(['-O'],FINAL,'--check')
with (FINAL/'.lock').open('a') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    locked=run([],FINAL,'--check')
need(good['exit_code']==0 and 'READY_NO_LEAN 0 completed' in good['stdout'],'valid check')
need(drift['exit_code']==1 and 'manifest or runner drift' in drift['stderr'],'runner drift')
need(duplicate['exit_code']==1 and 'warning baseline already exists' in duplicate['stderr'],'duplicate policy')
need(optimized['exit_code']==1 and 'without optimization' in optimized['stderr'],'optimized run')
need(locked['exit_code']==1 and 'BlockingIOError' in locked['stderr'],'lock')

module=runpy.run_path(str(RUNNER),run_name='reviewed_runner')
policy=module['warning_policies'](FINAL,module['plan']())[2]
original=(EVIDENCE/'compile.log').read_text()
original_source=OLD/'src/DiophantineConsistency/ModelDifferenceRing.lean'
new_source=FINAL/'src/DiophantineConsistency/ModelDifferenceRing.lean'
rerouted=original.replace(str(original_source),str(new_source))
need(module['warning_matches'](rerouted,new_source,policy),'complete normalized match')
need(not module['warning_matches'](rerouted+'\nwarning: mutation\n',new_source,policy),
     'additional diagnostic accepted')
need(not module['warning_matches'](original,original_source,None),'unregistered warning accepted')
need(module['warning_matches']('',new_source,None),'warning-free output rejected')

# Modify only the scratch source and baseline; retain the baseline mutation as
# an observation. The final registered overlay and evidence remain unchanged.
scratch_source=SCRATCH/'src/DiophantineConsistency/ModelDifferenceRing.lean'
original_bytes=scratch_source.read_bytes()
try:
    scratch_source.write_bytes(original_bytes+b'\n-- mutation control\n')
    source_mutation=run([],SCRATCH,'--check')
finally:
    scratch_source.write_bytes(original_bytes)
need(source_mutation['exit_code']==1 and 'source drift' in source_mutation['stderr'],
     'source mutation accepted')
with (SCRATCH/'warning-policies/002.log').open('a') as f: f.write('\nmutation control\n')
baseline_mutation=run([],SCRATCH,'--check')
need(baseline_mutation['exit_code']==1 and 'warning baseline drift' in baseline_mutation['stderr'],
     'baseline mutation accepted')
final=run([],FINAL,'--check')
need(final['exit_code']==0,'final overlay changed')
print(json.dumps({'status':'PASS_WARNING_POLICY_NO_LEAN_CONTROLS',
                  'runner_sha256':sha256(RUNNER.read_bytes()).hexdigest(),
                  'manifest_sha256':sha256((FINAL/'manifest.json').read_bytes()).hexdigest(),
                  'registration_sha256':sha256((FINAL/'warning-policies/002.json').read_bytes()).hexdigest(),
                  'normalized_log_sha256':sha256((FINAL/'warning-policies/002.log').read_bytes()).hexdigest(),
                  'checks':[good,drift,duplicate,optimized,locked,source_mutation,baseline_mutation,final],
                  'pure_checks':['normalized path match','additional diagnostic rejected',
                                 'unregistered warning rejected','warning-free output accepted'],
                  'scope':'registration and mutation controls only; no Lean compile or warning acceptability proof'},
                 indent=2,sort_keys=True))
