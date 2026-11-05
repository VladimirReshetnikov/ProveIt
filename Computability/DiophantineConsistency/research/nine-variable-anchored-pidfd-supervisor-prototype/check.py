#!/usr/bin/env python3
"""Synthetic session cleanup using proc-directory handles and an anchored leader.

No Lean or project worker is executed. This is a prototype, not a launch guard.
"""
import ctypes
import errno
import json
import os
import platform
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('run python3 -I -S -B')
if sys.platform!='linux' or platform.machine()!='x86_64':raise SystemExit('unsupported platform')
libc=ctypes.CDLL(None,use_errno=True);libc.syscall.restype=ctypes.c_long

def send(fd,sig):
    result=libc.syscall(ctypes.c_long(424),ctypes.c_int(fd),ctypes.c_int(sig),ctypes.c_void_p(0),ctypes.c_uint(0))
    if result<0:raise OSError(ctypes.get_errno(),os.strerror(ctypes.get_errno()))

def subreaper(value=None):
    old=ctypes.c_int()
    if libc.prctl(37,ctypes.byref(old),0,0,0):raise OSError(ctypes.get_errno(),'get subreaper')
    if value is not None and libc.prctl(36,int(value),0,0,0):raise OSError(ctypes.get_errno(),'set subreaper')
    return old.value

def snapshot(procfd):
    statfd=os.open('stat',os.O_RDONLY,dir_fd=procfd)
    try:line=os.read(statfd,8192).decode()
    finally:os.close(statfd)
    fields=line.rsplit(')',1)[1].split()
    return {'state':fields[0],'session':int(fields[3]),'starttime_ticks':int(fields[19])}

def live_or_zombie(pid):
    """Inspect without reaping: retaining the leader pins its numeric PID."""
    event=os.waitid(os.P_PID,pid,os.WEXITED|os.WNOHANG|os.WNOWAIT)
    return event is None

def scan(session,signum=None,signal_hook=None):
    """Open process first, inspect and signal that same stable proc handle."""
    found=[];errors=[]
    for path in Path('/proc').iterdir():
        if not path.name.isdecimal():continue
        fd=None
        try:
            fd=os.open(str(path),os.O_RDONLY|os.O_DIRECTORY)
            item=snapshot(fd)
            if item['session']!=session:continue
            pid=int(path.name);found.append((pid,item['state']))
            if signum is not None and item['state']!='Z':
                if signal_hook:signal_hook(pid)
                send(fd,signum)
        except OSError as exc:
            if exc.errno not in (errno.ENOENT,errno.ESRCH):errors.append((path.name,repr(exc)))
        finally:
            if fd is not None:os.close(fd)
    return found,errors

child='''import os,subprocess,sys,time
os.setpgid(0,0)
p=subprocess.Popen([sys.executable,"-I","-S","-B","-c","import time;time.sleep(30)"])
open(sys.argv[1],"w").write(str(os.getpid())+" "+str(p.pid))
time.sleep(30)
'''
leader_code='''import pathlib,subprocess,sys,time
marker=sys.argv[1];mode=sys.argv[2]
subprocess.Popen([sys.executable,"-I","-S","-B","-c",sys.argv[3],marker])
while not pathlib.Path(marker).exists():time.sleep(.01)
if mode=="leader_exit":sys.exit(0)
time.sleep(30)
'''

def run(mode,root):
    marker=root/(mode+'.pids');old=subreaper(1);p=None;reason=None;errors=[];observed=set();injected=[]
    try:
        p=subprocess.Popen([sys.executable,'-I','-S','-B','-c',leader_code,str(marker),mode,child],
                           start_new_session=True,stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
        deadline=time.monotonic()+4
        try:
            while time.monotonic()<deadline:
                is_live=live_or_zombie(p.pid)
                if marker.exists():
                    if mode=='monitor_exception':raise RuntimeError('synthetic monitor exception')
                    if not is_live:reason='leader exit';break
                    if mode in ('timeout','signal_error') and time.monotonic()>deadline-3:reason='timeout';break
                time.sleep(.02)
        except RuntimeError as exc:
            if str(exc)!='synthetic monitor exception':raise
            reason='monitor exception'
        if reason is None:raise RuntimeError('synthetic monitor timeout')
        childpid,grandpid=map(int,marker.read_text().split())
        def hook(pid):
            if mode=='signal_error' and not injected:
                injected.append(pid);raise PermissionError(errno.EPERM,'synthetic signal failure')
        cleanup_deadline=time.monotonic()+6;finished=False
        while time.monotonic()<cleanup_deadline:
            members,errs=scan(p.pid,signal.SIGTERM if time.monotonic()<cleanup_deadline-4 else signal.SIGKILL,hook)
            errors.extend(errs);observed.update(pid for pid,_ in members if pid!=p.pid)
            for pid in list(observed):
                try:os.waitpid(pid,os.WNOHANG)
                except ChildProcessError:pass
            # Do not reap the session leader before every descendant is gone.
            members,errs=scan(p.pid);errors.extend(errs)
            others=[item for item in members if item[0]!=p.pid]
            if not others and not live_or_zombie(p.pid):finished=True;break
            time.sleep(.05)
        if not finished:raise RuntimeError('session did not drain; refusing success')
        rc=p.wait(timeout=2)
        if Path('/proc',str(childpid)).exists() or Path('/proc',str(grandpid)).exists():
            raise RuntimeError('descendants not reaped')
        if mode=='signal_error' and (not injected or not errors):raise RuntimeError('signal failure not retained')
        if mode!='signal_error' and errors:raise RuntimeError('unexpected scan error '+repr(errors))
        return {'mode':mode,'reason':reason,'leader_reaped_last':True,'leader_returncode':rc,
                'descendants_reaped':True,'signal_error_retained':bool(errors)}
    finally:
        # Test cleanup also uses stable proc handles; no numeric kill/killpg.
        if p is not None and p.returncode is None:
            for _ in range(100):
                try:
                    members,_=scan(p.pid,signal.SIGKILL)
                    for pid,_ in members:
                        if pid!=p.pid:
                            try:os.waitpid(pid,os.WNOHANG)
                            except ChildProcessError:pass
                    if all(pid==p.pid for pid,_ in scan(p.pid)[0]) and not live_or_zombie(p.pid):break
                except (ChildProcessError,FileNotFoundError):break
                time.sleep(.05)
            p.wait(timeout=2)
        subreaper(old)

bystander=subprocess.Popen([sys.executable,'-I','-S','-B','-c','import time;time.sleep(30)'],start_new_session=True)
try:
    with tempfile.TemporaryDirectory(prefix='anchored-pidfd-supervisor-') as temp:
        results=[run(mode,Path(temp)) for mode in ('monitor_exception','leader_exit','timeout','signal_error')]
        if not live_or_zombie(bystander.pid):raise RuntimeError('outside-session bystander was signaled')
finally:
    bystander_fd=os.open('/proc/'+str(bystander.pid),os.O_RDONLY|os.O_DIRECTORY)
    try:send(bystander_fd,signal.SIGTERM)
    finally:os.close(bystander_fd)
    bystander.wait(timeout=2)
print(json.dumps({'status':'PASS_SYNTHETIC_ANCHORED_SESSION_CONTROLS','cases':results,
 'outside_session_bystander_untouched':True,
 'scope':'Owned synthetic Python sessions only; no Lean, project worker, or production resource supervisor.'},sort_keys=True))
