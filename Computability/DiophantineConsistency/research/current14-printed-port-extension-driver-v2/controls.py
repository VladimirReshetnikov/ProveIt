#!/usr/bin/env python3
"""Non-Lean behavioral controls for owned process monitoring; no project build."""
import json
import os
import subprocess
import sys
import time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import owned

HERE=Path(__file__).resolve().parent
sentinel=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)'],start_new_session=True)
results={}
try:
    code,seconds,receipt=owned.run([sys.executable,'-c','pass'],cwd=HERE,env=os.environ,
        stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=5,
        disk_check=lambda:True,poll_interval=.03)
    assert code==0 and receipt['exit']==0 and receipt['direct_child_reaped'] and receipt['session_drained']
    assert receipt['initial']['pgrp']==receipt['initial']['session']==receipt['pid']
    results['successful_owned_receipt']={'receipt':receipt,'sentinel_alive':sentinel.poll() is None}

    # Child forks a same-session descendant in another process group, then exits first.
    script=('import os,time\n'
            'if os.fork()==0:\n os.setpgid(0,0); time.sleep(0.8); os._exit(0)\n'
            'time.sleep(0.2)\n')
    def fault(): raise OSError('injected monitor failure')
    t=time.monotonic()
    real_popen=owned.subprocess.Popen; captured=[]
    def track(*args,**kwargs):
        child=real_popen(*args,**kwargs);captured.append(child.pid);return child
    owned.subprocess.Popen=track
    try:
        owned.run([sys.executable,'-c',script],cwd=HERE,env=os.environ,stdout=subprocess.DEVNULL,
                  stderr=subprocess.DEVNULL,timeout=10,disk_check=fault,poll_interval=.03)
        raise AssertionError('monitor failure did not propagate')
    except OSError as e:
        assert str(e)=='injected monitor failure'
    finally:
        owned.subprocess.Popen=real_popen
    elapsed=time.monotonic()-t
    try:
        os.waitpid(captured[0],os.WNOHANG)
        raise AssertionError('owned direct child was not reaped')
    except ChildProcessError:
        pass
    assert elapsed>=.65 and sentinel.poll() is None
    results['monitor_failure_waits_for_group']={'elapsed':round(elapsed,3),'direct_child_reaped':True,'sentinel_alive':True}

    # Normal threshold kills only authenticated owned group and fully reaps it.
    calls=[]
    try:
        owned.run([sys.executable,'-c','import time; time.sleep(30)'],cwd=HERE,env=os.environ,
                  stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=.12,
                  disk_check=lambda: True,report=calls.append,poll_interval=.03,grace=.1)
        raise AssertionError('timeout was not reported')
    except RuntimeError as e:
        assert str(e)=='owned process stopped by time/free-space bound'
    assert any('SIGTERM' in x for x in calls) and sentinel.poll() is None
    results['threshold_owned_group_only']={'events':calls,'sentinel_alive':True}

    # Refuse to signal if process identity can no longer be authenticated.
    real_identity=owned.identity;counter=[0]
    def mismatch(pid,initial):
        counter[0]+=1
        return real_identity(pid,initial) if counter[0]==1 else False
    owned.identity=mismatch
    events=[];t=time.monotonic()
    try:
        owned.run([sys.executable,'-c','import time; time.sleep(.45)'],cwd=HERE,env=os.environ,
                  stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=10,
                  disk_check=lambda:False,report=events.append,poll_interval=.03)
        raise AssertionError('identity mismatch was not reported')
    except RuntimeError as e:
        assert str(e)=='owned child identity lost; refusing signal'
    finally:
        owned.identity=real_identity
    elapsed=time.monotonic()-t
    assert elapsed>=.35 and not any('received SIG' in e for e in events) and sentinel.poll() is None
    results['identity_mismatch_passively_waits']={'elapsed':round(elapsed,3),'sentinel_alive':True}
    print(json.dumps({'status':'PASS','scope':'non-Lean test processes only', 'controls':results},indent=2,sort_keys=True))
finally:
    sentinel.terminate();sentinel.wait()
