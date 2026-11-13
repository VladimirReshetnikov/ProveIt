#!/usr/bin/env python3
"""Harmless actual-child interruption probe with explicit verified cleanup."""
import ctypes
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

DRIVER=Path(__file__).resolve().parent/'monitor-reviewed-bcf.py'
EXPECTED='bcf08ab90070b83b2f30c1f0116c7088e1791a5679a4310b3b0375ad47dc5a2b'


def need(ok,msg):
    if not ok:raise ValueError(msg)


def main():
    # The audit process adopts the fake child if the temporary wrapper dies;
    # it can then reap it instead of leaving a zombie behind.
    libc=ctypes.CDLL(None,use_errno=True)
    if libc.prctl(36,1,0,0,0)!=0:raise OSError(ctypes.get_errno(),'subreaper setup')
    h=hashlib.sha256(DRIVER.read_bytes()).hexdigest();need(h==EXPECTED,'reviewed historical driver pin')
    with tempfile.TemporaryDirectory(prefix='sigterm-monitor-audit-') as td:
        tmp=Path(td); marker=tmp/'fake.pid';log=tmp/'fake.log'
        child_code='import os,pathlib,time;pathlib.Path('+repr(str(marker))+').write_text(str(os.getpid()));time.sleep(30)'
        harness='''import importlib.util,os,pathlib,sys\np=pathlib.Path(sys.argv[1]);s=importlib.util.spec_from_file_location("audited_monitor",p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)\nm.monitored([sys.executable,"-I","-S","-c",sys.argv[3]],os.environ.copy(),pathlib.Path(sys.argv[2]))'''
        env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None)
        proc=subprocess.Popen([sys.executable,'-I','-S','-B','-c',harness,str(DRIVER),str(log),child_code],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True)
        pid=None; wrapper_exit=None;alive_after=None;cleanup_reaped=False
        try:
            deadline=time.monotonic()+8
            while not marker.exists() and proc.poll() is None and time.monotonic()<deadline:time.sleep(.02)
            need(marker.exists(),'fake compiler did not start')
            pid=int(marker.read_text());need(pid>1 and os.getpgid(pid)==pid and os.getsid(pid)==pid,'fake child group identity')
            proc.send_signal(signal.SIGTERM);stdout,stderr=proc.communicate(timeout=5);wrapper_exit=proc.returncode
            need(wrapper_exit==-signal.SIGTERM,'expected default SIGTERM exit '+repr((wrapper_exit,stdout,stderr)))
            state=Path(f'/proc/{pid}/stat').read_text().rsplit(') ',1)[1].split()[0]
            alive_after=state not in ('Z','X');need(alive_after,'fake child did not survive wrapper SIGTERM')
        finally:
            if proc.poll() is None:
                os.killpg(proc.pid,signal.SIGKILL);proc.wait(timeout=5)
            if pid is not None:
                try:
                    if os.getpgid(pid)==pid and os.getsid(pid)==pid:os.killpg(pid,signal.SIGKILL)
                except ProcessLookupError:pass
                deadline=time.monotonic()+5
                while time.monotonic()<deadline:
                    try:
                        got,_=os.waitpid(pid,os.WNOHANG)
                        if got==pid:cleanup_reaped=True;break
                    except ChildProcessError:
                        if not Path(f'/proc/{pid}').exists():cleanup_reaped=True
                        break
                    time.sleep(.02)
        need(cleanup_reaped and not Path(f'/proc/{pid}').exists(),'fake child cleanup not observed')
    print(json.dumps({'status':'CONFIRMED_SIGTERM_GAP_WITH_CLEANUP','driver_sha256':h,'wrapper_exit':wrapper_exit,
       'child_alive_after_wrapper_exit':alive_after,'fake_child_killed_and_reaped':cleanup_reaped,
       'scope':'One temporary fake child and one SIGTERM; no Lean process or live retry touched.'},indent=2))


if __name__=='__main__':main()
