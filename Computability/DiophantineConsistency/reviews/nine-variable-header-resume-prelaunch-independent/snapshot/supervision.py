#!/usr/bin/env python3
"""Owned-session supervision used by the staged header-inventory prototype."""
import os
import ctypes
import shutil
import signal
import subprocess
import time
from pathlib import Path

def available():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
    raise RuntimeError('MemAvailable missing')

def group_members(group, include_zombies=False):
    """Members of the owned session, including processes that changed groups."""
    members=[]
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit():continue
        try:
            fields=(proc/'stat').read_text().rsplit(')',1)[1].split()
            state, session=fields[0],int(fields[3])
            if session!=group or (state=='Z' and not include_zombies):continue
            values=[int(x.split()[1])*1024 for x in (proc/'status').read_text().splitlines() if x.startswith('VmRSS:')]
            if state!='Z' and len(values)!=1:raise RuntimeError('member RSS unavailable '+proc.name)
            members.append({'pid':int(proc.name),'rss':values[0] if values else 0,'state':state})
        except (FileNotFoundError,ProcessLookupError):continue
    return members

def subreaper(value=None):
    """Adopt and reap orphaned descendants, scoped to this supervisor process."""
    libc=ctypes.CDLL(None,use_errno=True);old=ctypes.c_int()
    if libc.prctl(37,ctypes.byref(old),0,0,0)!=0:raise OSError(ctypes.get_errno(),'PR_GET_CHILD_SUBREAPER')
    if value is not None and libc.prctl(36,int(value),0,0,0)!=0:
        raise OSError(ctypes.get_errno(),'PR_SET_CHILD_SUBREAPER')
    return old.value

def drain(group,leader):
    """Terminate the owned session, reap adopted descendants and verify drain."""
    error=None;observed=set();deadline=time.monotonic()+5
    while time.monotonic()<deadline:
        try:members=group_members(group,True)
        except Exception as exc:
            error=error or 'drain inspection: '+repr(exc)
            try:os.killpg(group,signal.SIGKILL)
            except ProcessLookupError:pass
            time.sleep(.05);continue
        observed.update(m['pid'] for m in members)
        for member in members:
            if member['state']!='Z':
                try:os.kill(member['pid'],signal.SIGTERM if time.monotonic()<deadline-3 else signal.SIGKILL)
                except ProcessLookupError:pass
        leader.poll()
        for pid in observed-{leader.pid}:
            try:os.waitpid(pid,os.WNOHANG)
            except (ChildProcessError,ProcessLookupError):pass
        try:
            if not group_members(group,True):return True,error
        except Exception as exc:error=error or 'final drain inspection: '+repr(exc)
        time.sleep(.05)
    return False,error or 'owned session still has members after termination/reap'

def supervise(cmd,log_path,*,cwd,env,timeout_seconds=60,rss_limit=7*1024**3//2,
              mem_floor=10*1024**3,disk_floor=4*1024**3,monitor_hook=None):
    """Run one child in a new session. `monitor_hook` is for synthetic tests."""
    if available()<mem_floor or shutil.disk_usage(cwd).free<disk_floor:
        raise RuntimeError('resource floor below launch threshold')
    previous_subreaper=subreaper(1)
    start=time.monotonic();samples=[];reason=None;leader=None;exit_code=None
    drain_error=None;drained=False;leftover_at_exit=[]
    try:
        with Path(log_path).open('x') as log:
            leader=subprocess.Popen(cmd,cwd=cwd,env=env,stdin=subprocess.DEVNULL,
                                    stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            try:
                while True:
                    exit_code=leader.poll()
                    members=group_members(leader.pid)
                    if exit_code is not None:
                        leftover_at_exit=[m['pid'] for m in members]
                        if members:reason='leader exited with live owned descendants'
                        break
                    mem=available();free=shutil.disk_usage(cwd).free;rss=sum(m['rss'] for m in members)
                    samples.append({'seconds':round(time.monotonic()-start,3),'available':mem,
                                    'free':free,'rss':rss,'members':members})
                    if monitor_hook:monitor_hook(members)
                    if mem<mem_floor:reason='available memory below floor'
                    elif free<disk_floor:reason='free disk below floor'
                    elif rss>=rss_limit:reason='group RSS at or above limit'
                    elif time.monotonic()-start>=timeout_seconds:reason='timeout'
                    if reason:break
                    time.sleep(.1)
            except Exception as exc:reason='monitor exception: '+repr(exc)
            finally:
                drained,drain_error=drain(leader.pid,leader)
                exit_code=leader.poll()
    finally:
        if leader is not None and not drained:
            drained2,extra=drain(leader.pid,leader)
            drained=drained2;drain_error=drain_error or extra
            exit_code=leader.poll()
        subreaper(previous_subreaper)
    return {'exit':exit_code,'reason':reason,'drained':drained,'drain_error':drain_error,
            'leftover_at_exit':leftover_at_exit,'samples':samples,
            'seconds':round(time.monotonic()-start,3),'session_id':None if leader is None else leader.pid,
            'command':cmd}
