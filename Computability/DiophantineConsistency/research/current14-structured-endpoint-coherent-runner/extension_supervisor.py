#!/usr/bin/env python3
"""Observe the v2 coordinator's actual exit, without killing its descendants."""
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import time
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent
TASK=HERE.parents[1]
ROOT=HERE.parents[3]
COORD=TASK/'research/current14-printed-port-extension-coordinator-v2/coordinator.py'
VERIFY=COORD.parent/'verify.py'
OUT=Path('/tmp/current14-printed-port-coordinator-supervisor-20261104')
COORD_OUT=Path('/tmp/current14-printed-port-extension-coordinator-v2-20261104')
PINS={COORD:'781b047c5da839917c7f6cfa3c877550f8eba0ef918b0dd08da4480d2a5b6a4c',
      VERIFY:'ba46edc8c3e6a48ffeb6afe087462bf798e1371f29a3586b3ac72bda340e6eb0'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
    if not c:raise ValueError(m)
def wait_owned(proc):
    """Persist until this exact Popen child has been reaped; return interruptions."""
    errors=[]
    while True:
        try:return proc.wait(),errors
        except BaseException as exc:
            errors.append(repr(exc))
            try:time.sleep(1)
            except BaseException as e:errors.append(repr(e))
def main():
    need(not OUT.exists() and not COORD_OUT.exists(),'refusing existing supervisor or coordinator output')
    for p,h in PINS.items():need(sha(p)==h,('coordinator pin mismatch',str(p)))
    # Read-only prerequisite gate before creating output or launching a child.
    spec=importlib.util.spec_from_file_location('supervised_coordinator',COORD)
    coordinator=importlib.util.module_from_spec(spec);spec.loader.exec_module(coordinator)
    need(not coordinator.driver.OUT.exists(),'extension output already exists')
    coordinator.context();need(coordinator.idle_lean(),'Lean slot not free')
    for p,h in PINS.items():need(sha(p)==h,('coordinator pin mismatch',str(p)))
    OUT.mkdir(); log=OUT/'coordinator.log'; receipt=OUT/'receipt.json'
    script_sha=sha(__file__);cmd=[sys.executable,'-I','-S','-B','-u',str(COORD),'--run']
    failure=None;proc=None;code=None;interruptions=[]
    with log.open('xb') as stream:
        try:
            proc=subprocess.Popen(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
            code,interruptions=wait_owned(proc)
            if interruptions:failure='supervisor wait interrupted'
        except BaseException as exc:
            failure=repr(exc)
            if proc is not None:
                code,interruptions=wait_owned(proc)
    statepath=COORD_OUT/'state.json'
    row={'status':'FAILED','command':cmd,'coordinator_sha256':PINS[COORD],
         'verify_sha256':PINS[VERIFY],'supervisor_sha256':script_sha,'child_pid':proc.pid if proc else None,
         'child_exit':code,'wait_interruptions':interruptions,'log':str(log),'log_sha256':sha(log),
         'failure':failure,'scope':'One directly observed coordinator child exit; no claim of full transitive ancestry.'}
    if statepath.is_file():
        row['coordinator_state_sha256']=sha(statepath)
        state=json.loads(statepath.read_text())
        if (failure is None and code==0 and not interruptions and state.get('status')=='PASS'
                and state.get('coordinator_sha256')==PINS[COORD] and state.get('verify_sha256')==PINS[VERIFY]
                and sha(__file__)==script_sha and all(sha(p)==h for p,h in PINS.items())):
            row['status']='PASS'
    with receipt.open('x') as f:json.dump(row,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps(row,sort_keys=True),flush=True)
    return 0 if row['status']=='PASS' else 1
if __name__=='__main__':
    try:raise SystemExit(main())
    except Exception as exc:print('REFUSED_OR_FAILED',repr(exc),file=sys.stderr);raise SystemExit(1)
