#!/usr/bin/env python3
"""Probe exception cleanup with a confirmed TERM-ignoring fake descendant."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import sys
import tempfile
import time

DRIVER=Path(__file__).resolve().parent/'monitor-reviewed-bcf.py'
EXPECTED='bcf08ab90070b83b2f30c1f0116c7088e1791a5679a4310b3b0375ad47dc5a2b'


def need(ok,msg):
    if not ok:raise ValueError(msg)


def state(pid):
    try:return Path(f'/proc/{pid}/stat').read_text().rsplit(') ',1)[1].split()[0]
    except (FileNotFoundError,ProcessLookupError):return None


def main():
    digest=hashlib.sha256(DRIVER.read_bytes()).hexdigest();need(digest==EXPECTED,'reviewed historical driver pin')
    spec=importlib.util.spec_from_file_location('reviewed_monitor',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    with tempfile.TemporaryDirectory(prefix='exception-monitor-audit-') as td:
        root=Path(td);ready=root/'descendant-ready'; seen=[]
        child='import os,pathlib,signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);pathlib.Path('+repr(str(ready))+').write_text(str(os.getpid()));time.sleep(30)'
        fake='import subprocess,sys,time;subprocess.Popen([sys.executable,"-I","-S","-c",'+repr(child)+']);time.sleep(30)'
        def failing_reader(pid):
            seen.append(pid);deadline=time.monotonic()+5
            while not ready.exists() and time.monotonic()<deadline:time.sleep(.02)
            need(ready.exists(),'descendant did not confirm its SIGTERM handler')
            raise RuntimeError('intentional audit monitor failure')
        try:
            m.monitored([sys.executable,'-I','-S','-c',fake],os.environ.copy(),root/'fake.log',rss_reader=failing_reader)
        except RuntimeError as e:
            need(str(e)=='intentional audit monitor failure','unexpected exception '+repr(e))
        else:raise ValueError('monitor exception did not propagate')
        leader=seen[0];descendant=int(ready.read_text())
        deadline=time.monotonic()+3
        while (state(leader) is not None or state(descendant) is not None) and time.monotonic()<deadline:time.sleep(.02)
        try:
            need(state(leader) is None and state(descendant) is None,'fake child or confirmed TERM-ignoring descendant not reaped')
        finally:
            # A failed control must not leave the fake test descendant alive.
            try:
                if os.getpgid(descendant)==leader and os.getsid(descendant)==leader:os.killpg(leader,signal.SIGKILL)
            except ProcessLookupError:pass
            try:os.waitpid(descendant,os.WNOHANG)
            except ChildProcessError:pass
    print(json.dumps({'status':'PASS_CONFIRMED_TERM_IGNORING_DESCENDANT_EXCEPTION_CONTROL',
      'driver_sha256':digest,'descendant_confirmed_ignored_sigterm_before_injection':True,
      'injected_exception_propagated':True,'fake_leader_reaped':True,'fake_same_group_descendant_reaped':True,
      'scope':'One verified process group only; escaped descendants, SIGKILL of the wrapper, race-free PID identity and whole-tree RSS remain outside this control.'},indent=2))


if __name__=='__main__':main()
