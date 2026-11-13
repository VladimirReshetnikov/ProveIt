#!/usr/bin/env python3
"""Record non-Lean controls and current guarded preflight refusal/success."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent
ROOT=P.parents[3]
OUT=Path('/tmp/ordinary13-p73-share91-graph-attempt01-20261111')
assert not os.path.lexists(OUT), 'output already exists; refusing observation'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def call(args):
    p=subprocess.run([sys.executable,'-I','-S','-B',*map(str,args)],cwd=ROOT,
                     stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180)
    return {'exit_code':p.returncode,'stdout':p.stdout.decode(),'stderr':p.stderr.decode()}
controls=call([P/'controls.py'])
inspection=call([P/'run.py','--inspect'])
preflight=call([P/'run.py','--preflight'])
assert controls['exit_code']==0 and 'PASS_NON_LEAN_CONTROLS' in controls['stdout']
assert inspection['exit_code']==0 and 'READ_ONLY_INSPECTION_NOT_LAUNCH_APPROVAL' in inspection['stdout']
assert preflight['exit_code'] in (0,1)
if preflight['exit_code'] == 1:
    assert 'disk_floor' in preflight['stderr'] or 'host_memory_floor' in preflight['stderr'] or 'total_timeout' in preflight['stderr']
assert not os.path.lexists(OUT), 'no-Lean controls created the build output'
out={'status':'NON_LEAN_CONTROLS_RECORDED',
     'source_sha256':{p.name:sha(p) for p in (P/'run.py',P/'plan.json',P/'controls.py',P/'capture_controls.py')},
     'controls':controls,'read_only_inspection':inspection,'guarded_preflight':preflight,
     'output_path_absent':True,'scope':'No Lean or build tree. Resource and source observations are point-in-time, not launch approval.'}
target=P/'controls-observation.json'
if target.exists(): raise SystemExit('refusing to overwrite observation')
target.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':out['status'],'controls_exit':controls['exit_code'],
                  'inspection_exit':inspection['exit_code'],'preflight_exit':preflight['exit_code'],
                  'output_path_absent':True},sort_keys=True))
