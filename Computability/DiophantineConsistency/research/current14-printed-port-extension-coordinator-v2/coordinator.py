#!/usr/bin/env python3
"""Record and validate the 61-module extension driver's actual process exit."""
import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent
TASK=HERE.parents[1]
ROOT=HERE.parents[3]
DRIVER_DIR=TASK/'research/current14-printed-port-extension-driver-v2'
sys.path.insert(0,str(HERE));sys.path.insert(0,str(DRIVER_DIR))
from verify import verify_terminal
spec=importlib.util.spec_from_file_location('current14_extension_driver',DRIVER_DIR/'driver.py')
driver=importlib.util.module_from_spec(spec);spec.loader.exec_module(driver)
OUT=Path('/tmp/current14-printed-port-extension-coordinator-v2-20261104')
DRIVER_SHA='720a5a8ad2bb2cf05dafc5bd68afafbea9f452d343dbfb7e3b77628795492771'
GUARDS_SHA='e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3'
OWNED_SHA='60859f538a7069d90f3f44871613fd2ef96c0ea738c9313cd1971d851b4b33ca'
MIN_MEMORY=10*1024**3
MIN_DISK=4_000_000_000
def need(condition,message):
    if not condition:raise ValueError(message)
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def available():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
    raise RuntimeError('MemAvailable unavailable')
def idle_lean():
    ps=subprocess.run(['ps','-eo','pid=,stat=,comm='],check=True,text=True,stdout=subprocess.PIPE).stdout
    return not any(len(x)==3 and x[2]=='lean' and not x[1].startswith('Z') for x in (line.split() for line in ps.splitlines()))
def pinned():
    need(sha(DRIVER_DIR/'driver.py')==DRIVER_SHA and sha(DRIVER_DIR/'guards.py')==GUARDS_SHA and
         sha(DRIVER_DIR/'owned.py')==OWNED_SHA,
         'reviewed extension driver or guards changed')
def context():
    pinned();ctx=driver.preflight()
    ctx.update(base_lib=driver.BASE_DIR/'lib',workspace_root=driver.ROOT,
               package_root=driver.PKG,tool_root=driver.TOOL)
    need(available()>=MIN_MEMORY,'MemAvailable below 10 GiB before launch')
    need(shutil.disk_usage('/tmp').free>=MIN_DISK,'disk free below 4 GB before launch')
    return ctx
def final_hashes():
    return {'base_state_sha256':sha(driver.BASE_STATE),'watchdog_sha256':sha(driver.WATCHDOG),
            'driver_sha256':DRIVER_SHA,'guards_sha256':GUARDS_SHA,'owned_sha256':OWNED_SHA,
            'manifest_sha256':driver.PINS[driver.SNAP/'manifest.json'],
            'provider_sha256':driver.PINS[driver.PROVIDER]}
def settle_monitor_failure(proc,state,save,exc):
    if proc is not None:
        state.update(status='MONITOR_FAILURE_WAITING_FOR_CHILD',failure=repr(exc))
        try:save()
        except BaseException:pass
        # Keep owning and waiting even if an emergency save or wait is interrupted.
        # A permanently failing wait can leave this coordinator running indefinitely.
        while True:
            try:
                state['child_exit_after_monitor_failure']=proc.wait()
                break
            except BaseException:
                try:time.sleep(1)
                except BaseException:pass
def run(ctx):
    need(not OUT.exists() and not driver.OUT.exists(),'refusing existing coordinator or extension output')
    need(idle_lean(),'Lean slot is not free')
    initial=final_hashes();script_hash=sha(__file__);verify_hash=sha(HERE/'verify.py')
    OUT.mkdir();statepath=OUT/'state.json';log=OUT/'extension-process.log'
    cmd=[sys.executable,'-I','-S','-B','-u',str(DRIVER_DIR/'driver.py'),'--run']
    state={'status':'RUNNING','command':cmd,'initial_hashes':initial,'coordinator_sha256':script_hash,
           'verify_sha256':verify_hash,'samples':[],
           'scope':'Actual child exit and terminal direct-state audit; package-transitive, dynamic and transient ancestry inherited.'}
    def save():
        q=OUT/'state.tmp';q.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');q.replace(statepath)
    start=time.monotonic();save();proc=None
    try:
        with log.open('x') as stream:
            proc=subprocess.Popen(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
            state['child_pid']=proc.pid;save()
            while proc.poll() is None:
                sample={'elapsed_seconds':round(time.monotonic()-start,2),'free_bytes':shutil.disk_usage('/tmp').free,
                        'memavailable_bytes':available()}
                try:
                    inner=json.loads((driver.OUT/'state.json').read_text())
                    sample.update({k:inner.get(k) for k in ('status','phase','index','module')})
                except (FileNotFoundError,json.JSONDecodeError):pass
                state['samples'].append(sample);save();time.sleep(10)
            code=proc.wait()
        state.update(child_exit=code,elapsed_seconds=round(time.monotonic()-start,2),process_log_sha256=sha(log))
        need(code==0,('extension process failed',code))
        terminal=driver.OUT/'state.json';need(terminal.is_file(),'extension terminal state missing')
        terminal_sha=sha(terminal);inner=json.loads(terminal.read_text())
        pinned();need(final_hashes()==initial,'base/watchdog/static pins changed')
        after=driver.preflight();after.update(base_lib=driver.BASE_DIR/'lib',workspace_root=driver.ROOT,
                                              package_root=driver.PKG,tool_root=driver.TOOL)
        need(after['external_guard']==ctx['external_guard'] and after['order']==ctx['order'],'preflight context drift')
        helper={'need':need,'digest':driver.digest,'check_guard':driver.check_guard,'suffixes':driver.SUFFIXES}
        validation=verify_terminal(inner,code,after,driver.OUT,helper,initial,proc.pid)
        finalctx=driver.preflight()
        need(finalctx['external_guard']==ctx['external_guard'] and finalctx['order']==ctx['order'],
             'base, provider or extension context changed during terminal validation')
        need(sha(terminal)==terminal_sha and sha(__file__)==script_hash and sha(HERE/'verify.py')==verify_hash,
             'terminal state or coordinator changed during validation')
        need(final_hashes()==initial,'base/watchdog pins changed during terminal validation')
        state.update(status='PASS',extension_state_sha256=terminal_sha,validation=validation);save()
        print('PASS: actual extension exit and terminal state verified',flush=True)
    except BaseException as exc:
        # The extension driver starts Lean in separate sessions. Do not kill
        # only our process group and silently orphan that child. If monitoring
        # fails while the driver is live, record that condition and continue
        # waiting for its actual exit; no PASS can result from this branch.
        settle_monitor_failure(proc,state,save,exc)
        state.update(status='FAILED',failure=repr(exc));save();raise
def main():
    parser=argparse.ArgumentParser();group=parser.add_mutually_exclusive_group()
    group.add_argument('--check',action='store_true');group.add_argument('--run',action='store_true')
    args=parser.parse_args()
    need(not OUT.exists() and not driver.OUT.exists(),'coordinator or extension output already exists')
    ctx=context()
    print(json.dumps({'status':'PREFLIGHT_ONLY','base_modules':len(ctx['manifest']['order']),
                      'extension_modules':len(ctx['order']),'free_bytes':shutil.disk_usage('/tmp').free,
                      'memavailable_bytes':available()},sort_keys=True),flush=True)
    if args.run:run(ctx)
if __name__=='__main__':
    try:main()
    except Exception as exc:print('REFUSED_OR_FAILED',repr(exc),file=sys.stderr);raise SystemExit(1)
