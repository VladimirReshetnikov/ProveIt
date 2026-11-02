#!/usr/bin/env python3
"""External-signal test on the corrected monitor with temporary fake children."""
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

DRIVER=Path(__file__).resolve().parent/'driver-2c8.py'
EXPECTED='2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'


def need(ok,msg):
    if not ok:raise ValueError(msg)


def state(pid):
    try:return Path(f'/proc/{pid}/stat').read_text().rsplit(') ',1)[1].split()[0]
    except (FileNotFoundError,ProcessLookupError):return None


def main():
    need(hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'corrected driver pin')
    libc=ctypes.CDLL(None,use_errno=True)
    if libc.prctl(36,1,0,0,0)!=0:raise OSError(ctypes.get_errno(),'subreaper setup')
    results=[]
    for sig in (signal.SIGTERM,signal.SIGINT):
      with tempfile.TemporaryDirectory(prefix='corrected-monitor-signals-') as td:
        root=Path(td);leaderfile=root/'leader';ready=root/'descendant-ready';log=root/'fake.log'
        desc='import os,pathlib,signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);pathlib.Path('+repr(str(ready))+').write_text(str(os.getpid()));time.sleep(30)'
        fake='import os,pathlib,subprocess,sys,time;pathlib.Path('+repr(str(leaderfile))+').write_text(str(os.getpid()));subprocess.Popen([sys.executable,"-I","-S","-c",'+repr(desc)+']);time.sleep(30)'
        harness='''import importlib.util,json,os,pathlib,sys\np=pathlib.Path(sys.argv[1]);s=importlib.util.spec_from_file_location("corrected_monitor",p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)\nc,peak,reason=m.monitored([sys.executable,"-I","-S","-c",sys.argv[3]],os.environ.copy(),pathlib.Path(sys.argv[2]));print(json.dumps({"child_exit":c,"peak":peak,"reason":reason}),flush=True)'''
        env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None)
        proc=subprocess.Popen([sys.executable,'-I','-S','-B','-c',harness,str(DRIVER),str(log),fake],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True)
        leader=descendant=None; wrapper_exit=None;result=None
        try:
            deadline=time.monotonic()+8
            while not ready.exists() and proc.poll() is None and time.monotonic()<deadline:time.sleep(.02)
            need(ready.exists() and leaderfile.exists(),'fake descendant did not become ready')
            leader=int(leaderfile.read_text());descendant=int(ready.read_text())
            need(os.getpgid(leader)==leader and os.getsid(leader)==leader and os.getpgid(descendant)==leader,'fake group identity')
            proc.send_signal(sig);stdout,stderr=proc.communicate(timeout=10);wrapper_exit=proc.returncode
            need(wrapper_exit==0 and not stderr,'harness failed '+repr((wrapper_exit,stdout,stderr)))
            result=json.loads(stdout);need(result['reason']=='interrupt_signal_'+str(int(sig)) and result['child_exit']!=0,'interruption result')
            deadline=time.monotonic()+3
            while (state(leader) is not None or state(descendant) is not None) and time.monotonic()<deadline:time.sleep(.02)
            need(state(leader) is None and state(descendant) is None,'same-group test processes not reaped')
        finally:
            if proc.poll() is None:
                try:os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                proc.wait(timeout=5)
            if leader is not None:
                try:
                    if descendant is not None and os.getpgid(descendant)==leader and os.getsid(descendant)==leader:os.killpg(leader,signal.SIGKILL)
                except ProcessLookupError:pass
                for pid in (leader,descendant):
                    if pid is None:continue
                    try:os.waitpid(pid,os.WNOHANG)
                    except ChildProcessError:pass
        results.append({'signal':int(sig),'harness_exit':wrapper_exit,'monitored_child_exit':result['child_exit'],
                        'reason':result['reason'],'leader_reaped':True,'confirmed_term_ignoring_descendant_reaped':True})
    print(json.dumps({'status':'PASS_CORRECTED_EXTERNAL_SIGNAL_CONTROLS','driver_sha256':EXPECTED,'results':results,
      'scope':'Two temporary same-group controls only; no Lean or real replay. Escape, PID races, forced wrapper SIGKILL, whole-tree RSS and continuous quotas are not covered.'},indent=2))


if __name__=='__main__':main()
