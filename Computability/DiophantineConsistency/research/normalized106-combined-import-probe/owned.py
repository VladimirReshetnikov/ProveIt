"""Linux owned-session process monitoring; no subprocess is reaped before group drain.

A monitoring exception causes a passive wait, potentially indefinitely. Processes
that escape the session and forced termination of this Python process are outside
this helper's scope. The direct child is not reaped until cleanup is complete.
"""
import os
import signal
import subprocess
import time
from pathlib import Path


def stat(pid):
    raw = Path('/proc', str(pid), 'stat').read_text()
    fields = raw.rsplit(')', 1)[1].split()
    return {'state': fields[0], 'ppid': int(fields[1]), 'pgrp': int(fields[2]),
            'session': int(fields[3]), 'start': int(fields[19])}


def group_live(pid):
    # An unreadable surviving process is not evidence that the group drained.
    live = []
    for entry in Path('/proc').iterdir():
        if not entry.name.isdecimal():
            continue
        try:
            info = stat(int(entry.name))
        except FileNotFoundError:
            continue
        if info['session'] == pid and info['state'] not in ('Z', 'X'):
            live.append(int(entry.name))
    return live


def terminal(pid):
    return os.waitid(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT) is not None


def identity(pid, initial):
    current = stat(pid)
    return (current['start'] == initial['start'] and current['ppid'] == os.getpid()
            and current['pgrp'] == pid and current['session'] == pid)


def run(cmd, *, cwd, env, stdout, stderr, timeout, disk_check, report=lambda message: None,
        poll_interval=1.0, grace=20.0, on_reap=lambda code, lifecycle: None):
    started = time.monotonic()
    proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=stdout, stderr=stderr,
                            start_new_session=True)
    failure = None
    initial = None
    signaled = False
    deadline = None
    killed = False
    try:
        initial = stat(proc.pid)
        if not identity(proc.pid, initial):
            raise RuntimeError('owned child identity not established')
        while True:
            within_bounds = disk_check(proc.pid)
            if terminal(proc.pid) and not group_live(proc.pid):
                if not within_bounds or time.monotonic()-started>=timeout:
                    failure=RuntimeError('owned process finished outside resource bounds')
                break
            if not signaled and (time.monotonic() - started >= timeout or not within_bounds):
                failure = RuntimeError('owned process stopped by time/free-space bound')
                if not identity(proc.pid, initial):
                    raise RuntimeError('owned child identity lost; refusing signal')
                os.killpg(proc.pid, signal.SIGTERM)
                signaled = True
                deadline = time.monotonic() + grace
                report('owned session received SIGTERM')
            if signaled and not killed and time.monotonic() >= deadline:
                if not identity(proc.pid, initial):
                    raise RuntimeError('owned child identity lost; refusing SIGKILL')
                os.killpg(proc.pid, signal.SIGKILL)
                killed = True
                report('owned session received SIGKILL')
            time.sleep(poll_interval)
    except BaseException as exc:
        failure = exc
        # Never return while an owned child may still be alive. If /proc or
        # waitid is unavailable, keep waiting rather than treating it as drain.
        while True:
            try:
                report('MONITOR_FAILURE_WAITING pid=%s error=%r' % (proc.pid, exc))
            except BaseException:
                pass
            try:
                if terminal(proc.pid) and not group_live(proc.pid):
                    break
            except BaseException:
                pass
            try:
                time.sleep(max(poll_interval, 0.05))
            except BaseException:
                pass
    while True:
        try:
            code = proc.wait()
            break
        except BaseException as exc:
            failure = exc
            try:time.sleep(1)
            except BaseException:pass
    elapsed = round(time.monotonic() - started, 3)
    lifecycle = {'pid':proc.pid,'initial':initial,'session_drained':True,
                 'direct_child_reaped':True,'exit':code,'elapsed_seconds':elapsed}
    try:
        on_reap(code, lifecycle)
    except BaseException as exc:
        failure = exc
    if failure is not None:
        raise failure
    return code, elapsed, lifecycle
