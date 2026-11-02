#!/usr/bin/env python3
"""Deterministic negative controls for the sampled child monitor."""
import importlib.util
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('optimized Python rejected')
source=Path(__file__).resolve().parent/'replay.py'
spec=importlib.util.spec_from_file_location('denominator_replay_tested',source)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

def state(pid):
    try:return Path(f'/proc/{pid}/stat').read_text().rsplit(') ',1)[1].split()[0]
    except (FileNotFoundError,ProcessLookupError):return None

with tempfile.TemporaryDirectory(prefix='ipra-denominator-monitor-test-') as t:
    root=Path(t)
    cmd=[sys.executable,'-I','-S','-c','import time; time.sleep(1.2)']
    code,peak,reason=m.monitored(cmd,os.environ.copy(),root/'happy.log')
    if code!=0 or peak<=0 or reason is not None:raise AssertionError(('happy',code,peak,reason))
    print('PASS observed child success and RSS sample')
    code,peak,reason=m.monitored([sys.executable,'-I','-S','-c','import time;time.sleep(10)'],
                                  os.environ.copy(),root/'missing.log',rss_reader=lambda _:None)
    if reason!='rss_unavailable_while_unreaped' or code==0 or peak!=0:
        raise AssertionError(('missing RSS accepted',code,peak,reason))
    print('PASS missing RSS stops verified group and reaps leader')
    transient=[]
    def transient_reader(pid):
        transient.append(pid)
        return None if len(transient)==1 else m.rss_bytes(pid)
    code,peak,reason=m.monitored(cmd,os.environ.copy(),root/'transient.log',rss_reader=transient_reader)
    if code!=0 or peak<=0 or reason is not None or len(transient)<2:
        raise AssertionError(('transient RSS did not recover',code,peak,reason))
    print('PASS transient missing RSS requires a subsequent valid sample')
    def exit_without_sample(_):
        time.sleep(.5)
        return None
    code,peak,reason=m.monitored([sys.executable,'-I','-S','-c','import time;time.sleep(.1)'],
                                  os.environ.copy(),root/'no-sample.log',rss_reader=exit_without_sample)
    if code!=0 or peak!=0 or reason!='no_rss_observation':
        raise AssertionError(('exit without RSS accepted',code,peak,reason))
    print('PASS child exit without any RSS observation fails closed')
    calls=[]
    def exit_after_sample(pid):
        calls.append(pid)
        if len(calls)==1:
            return m.rss_bytes(pid)
        time.sleep(.6)
        return None
    code,peak,reason=m.monitored(cmd,os.environ.copy(),root/'exit-race.log',rss_reader=exit_after_sample)
    if code!=0 or peak<=0 or reason is not None or len(calls)<2:
        raise AssertionError(('observed exit after RSS sample rejected',code,peak,reason))
    print('PASS child exit after prior valid RSS sample resolves exit race')
    seen=[]
    childfile=root/'descendant.pid'
    script=('import subprocess,sys,time; '
            'p=subprocess.Popen([sys.executable,"-I","-S","-c",'
            '"import signal,time; signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(20)"]); '
            f'open({str(childfile)!r},"w").write(str(p.pid)); '
            'time.sleep(20)')
    def fail_reader(pid):
        seen.append(pid)
        deadline=time.monotonic()+5
        while not childfile.exists() and time.monotonic()<deadline:time.sleep(.02)
        if not childfile.exists():raise AssertionError('descendant did not start')
        raise RuntimeError('injected RSS monitor failure')
    try:
        m.monitored([sys.executable,'-I','-S','-c',script],os.environ.copy(),root/'exception.log',rss_reader=fail_reader)
        raise AssertionError('injected exception was accepted')
    except RuntimeError as exc:
        if str(exc)!='injected RSS monitor failure':raise
    leader=seen[0];descendant=int(childfile.read_text())
    if state(leader) is not None:raise AssertionError(('leader not reaped',leader,state(leader)))
    deadline=time.monotonic()+3
    while state(descendant) is not None and time.monotonic()<deadline:time.sleep(.02)
    if state(descendant) is not None:raise AssertionError(('descendant not reaped',descendant,state(descendant)))
    print('PASS monitor exception terminates verified group and reaps leader and descendant')
    # Signal the actual wrapper, not the child group. The fake descendant
    # reports ready only after installing its SIGTERM-ignoring handler.
    leaderfile=root/'signal-leader.pid'
    readyfile=root/'signal-descendant.pid'
    descendant_code=('import signal,time,pathlib,os; '
                     'signal.signal(signal.SIGTERM,signal.SIG_IGN); '
                     f'pathlib.Path({str(readyfile)!r}).write_text(str(os.getpid())); '
                     'time.sleep(30)')
    child_code=('import os,pathlib,subprocess,sys,time; '
                f'pathlib.Path({str(leaderfile)!r}).write_text(str(os.getpid())); '
                f'subprocess.Popen([sys.executable,"-I","-S","-c",{descendant_code!r}]); '
                'time.sleep(30)')
    launcher=('import importlib.util,os,pathlib,sys; '
              f's=importlib.util.spec_from_file_location("testmonitor",{str(source)!r}); '
              'm=importlib.util.module_from_spec(s);s.loader.exec_module(m); '
              f'c,p,r=m.monitored([sys.executable,"-I","-S","-c",{child_code!r}],'
              f'os.environ.copy(),pathlib.Path({str(root / "signal.log")!r})); '
              'sys.exit(17 if r=="interrupt_signal_15" else 18)')
    wrapper=subprocess.Popen([sys.executable,'-I','-S','-c',launcher],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    try:
        deadline=time.monotonic()+8
        while not readyfile.exists() and wrapper.poll() is None and time.monotonic()<deadline:time.sleep(.02)
        if not readyfile.exists():raise AssertionError('signal-control descendant did not become ready')
        signal_leader=int(leaderfile.read_text());signal_descendant=int(readyfile.read_text())
        os.kill(wrapper.pid,signal.SIGTERM)
        stdout,stderr=wrapper.communicate(timeout=8)
        if wrapper.returncode!=17:
            raise AssertionError(('signal wrapper did not report interruption',wrapper.returncode,stdout,stderr))
        if state(signal_leader) is not None or state(signal_descendant) is not None:
            raise AssertionError(('signal-control child not reaped',state(signal_leader),state(signal_descendant)))
        print('PASS external SIGTERM terminates verified group and reaps leader and descendant')
    finally:
        if wrapper.poll() is None:
            wrapper.kill();wrapper.wait()
        if leaderfile.exists():
            leaderpid=int(leaderfile.read_text())
            try:
                if os.getpgid(leaderpid)==leaderpid:
                    os.killpg(leaderpid,signal.SIGKILL)
            except ProcessLookupError:
                pass
            deadline=time.monotonic()+3
            while time.monotonic()<deadline:
                try:child,_=os.waitpid(-leaderpid,os.WNOHANG)
                except ChildProcessError:break
                if child==0:time.sleep(.02)
    print('PASS_DENOMINATOR_MONITOR_NEGATIVE_CONTROLS')
