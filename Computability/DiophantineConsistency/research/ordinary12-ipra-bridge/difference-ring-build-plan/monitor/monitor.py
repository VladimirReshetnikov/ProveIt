#!/usr/bin/env python3
"""Sample a fresh run directory and stop its process group on budget violations.

Sampling is advisory, not a quota or reservation. Children must honor the
provided MONITOR_OUTPUT and TMPDIR; other write paths are not monitored.
"""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
from path_guard import fresh_output

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('sampled replay rejects optimized Python and PYTHONOPTIMIZE')

RESERVE = 4 * 1024**3
BUDGET = 512 * 1024**2


def process_start_ticks(pid):
    """Linux process start identity; None means it cannot be safely checked."""
    try:
        return int(Path(f'/proc/{pid}/stat').read_text().rsplit(') ', 1)[1].split()[19])
    except (OSError, ValueError, IndexError):
        return None


def sampled_tree_bytes(root):
    """Logical file sizes, without following links; excludes filesystem overhead."""
    size = 0
    for directory, dirs, files in os.walk(root, followlinks=False):
        for name in files:
            path = Path(directory) / name
            try:
                if not path.is_symlink():
                    size += path.stat().st_size
            except FileNotFoundError:
                continue
        dirs[:] = [name for name in dirs if not (Path(directory) / name).is_symlink()]
    return size


def disk_bytes(path):
    st = os.statvfs(path)
    return st.f_bavail * st.f_frsize


def command_inputs(command):
    """Protect named Lean-builder inputs; arbitrary child paths need --protect."""
    found=[]
    for i,arg in enumerate(command):
        for flag in ('--snapshot','--provider-receipt','--foundation-input'):
            if arg==flag:
                if i+1>=len(command):raise ValueError(('missing input flag value',flag))
                found.append(Path(command[i+1]))
            elif arg.startswith(flag+'='):
                found.append(Path(arg[len(flag)+1:]))
    for i,arg in enumerate(command):
        value=None
        if arg=='--provider-receipt' and i+1<len(command):value=command[i+1]
        elif arg.startswith('--provider-receipt='):value=arg.split('=',1)[1]
        if value is not None:
            data=json.loads(Path(value).read_text())
            for key in ('root','overlay'):
                item=data.get(key)
                if not isinstance(item,str) or not Path(item).is_absolute() or not Path(item).is_dir():
                    raise ValueError(('invalid or missing provider root',key))
                found.append(Path(item))
    return found


def terminate_group(proc, grace):
    """Signal the entire session, including children after leader exit."""
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    deadline = time.monotonic() + grace
    while time.monotonic() < deadline:
        try:
            os.killpg(proc.pid, 0)
        except ProcessLookupError:
            break
        proc.poll()
        time.sleep(min(0.05, max(0, deadline - time.monotonic())))
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    return proc.wait()


def run(run_dir, command, *, reserve=RESERVE, budget=BUDGET, interval=1.0,
        grace=2.0, sensor=None, protected=()):
    """Run once. `sensor` is injection for unit tests only, never the CLI."""
    if reserve < 0 or budget <= 0 or interval <= 0 or grace < 0 or not command:
        raise ValueError('invalid monitor settings')
    protected=(*protected,*command_inputs(command))
    run_dir = fresh_output(run_dir, protected)
    # Recheck immediately before creation; this does not close TOCTOU races.
    run_dir = fresh_output(run_dir, protected)
    run_dir.mkdir(parents=False, exist_ok=False)
    if run_dir.is_symlink() or run_dir.resolve(strict=True) != run_dir:
        raise ValueError('output changed during creation')
    out = run_dir / 'child-output'
    tmp = run_dir / 'tmp'
    tmp.mkdir()
    log = run_dir / 'child.log'
    state_path = run_dir / 'terminal.json'
    get_sample = sensor or (lambda: (disk_bytes(run_dir), sampled_tree_bytes(run_dir)))
    start_free, start_size = get_sample()
    result = {'status': 'RUNNING', 'command': command, 'run_dir': str(run_dir),
              'child_output': str(out), 'tmpdir': str(tmp), 'log': str(log),
              'reserve_bytes': reserve, 'budget_bytes': budget,
              'sample_interval_seconds': interval, 'initial_free_bytes': start_free,
              'initial_logical_bytes': start_size, 'sample_count': 1,
              'minimum_free_bytes': start_free, 'maximum_logical_bytes': start_size,
              'sampled_only': True, 'outer_exit_code': None, 'violation': None,
              'scope': 'Observed logical sizes in this run directory and host free space only; no quota, total-write confinement or continuous reserve guarantee.'}
    def save():
        temp = state_path.with_suffix('.tmp')
        temp.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        os.replace(temp, state_path)
    def sample():
        free, size = get_sample()
        result['sample_count'] += 1
        result['minimum_free_bytes'] = min(result['minimum_free_bytes'], free)
        result['maximum_logical_bytes'] = max(result['maximum_logical_bytes'], size)
        return free, size
    def fail_reason(free, size):
        if free < reserve:
            return 'free_space_below_sampled_threshold'
        if size > budget:
            return 'logical_size_above_sampled_budget'
        return None
    stop = fail_reason(start_free, start_size)
    if stop:
        result.update(status='STOPPED_BEFORE_LAUNCH', violation=stop)
        save()
        return result
    env = os.environ.copy()
    env['MONITOR_OUTPUT'] = str(out)
    env['TMPDIR'] = str(tmp)
    for name in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT', 'PYTHONOPTIMIZE'):
        env.pop(name, None)
    requested = []
    old_handlers = {}
    def handler(signum, _frame):
        requested.append(signum)
    for sig in (signal.SIGINT, signal.SIGTERM):
        old_handlers[sig] = signal.getsignal(sig)
        signal.signal(sig, handler)
    proc = None
    try:
        with log.open('xb') as stream:
            proc = subprocess.Popen(command, stdout=stream, stderr=subprocess.STDOUT,
                                    env=env, start_new_session=True)
            result['pid'] = proc.pid
            result['pid_start_ticks'] = process_start_ticks(proc.pid)
            save()
            while True:
                free, size = sample()
                stop = fail_reason(free, size)
                if requested:
                    stop = 'interrupt_signal_' + str(requested[0])
                if stop:
                    code = terminate_group(proc, grace)
                    result.update(status='STOPPED', violation=stop, outer_exit_code=code)
                    break
                code = proc.poll()
                if code is not None:
                    # A successful leader can leave a background writer in its process group.
                    try:
                        os.killpg(proc.pid, 0)
                    except ProcessLookupError:
                        lingering = False
                    else:
                        lingering = True
                    if lingering:
                        terminate_group(proc, grace)
                        result.update(status='STOPPED', violation='lingering_process_group', outer_exit_code=code)
                    else:
                        result.update(status='EXITED', outer_exit_code=code)
                    break
                time.sleep(interval)
    except BaseException as exc:
        if proc is not None:
            result['outer_exit_code'] = terminate_group(proc, grace)
        result.update(status='MONITOR_ERROR', violation=repr(exc))
        raise
    finally:
        for sig, old in old_handlers.items():
            signal.signal(sig, old)
        # Final sample also detects a threshold crossing near process exit.
        try:
            free, size = sample()
            if result['status'] == 'EXITED':
                final_violation = fail_reason(free, size)
                if final_violation:
                    result.update(status='STOPPED', violation=final_violation)
        finally:
            save()
    return result


def main():
    if not sys.flags.isolated or not sys.flags.no_site:
        raise RuntimeError('monitor requires isolated Python startup (-I -S)')
    ap = argparse.ArgumentParser()
    ap.add_argument('--run-dir', type=Path, required=True)
    ap.add_argument('--reserve-bytes', type=int, default=RESERVE)
    ap.add_argument('--budget-bytes', type=int, default=BUDGET)
    ap.add_argument('--interval', type=float, default=1.0)
    ap.add_argument('--grace', type=float, default=2.0)
    ap.add_argument('--protect', type=Path, action='append', default=[])
    ap.add_argument('command', nargs=argparse.REMAINDER)
    a = ap.parse_args()
    command = a.command[1:] if a.command[:1] == ['--'] else a.command
    result = run(a.run_dir, command, reserve=a.reserve_bytes, budget=a.budget_bytes,
                 interval=a.interval, grace=a.grace, protected=a.protect)
    print(json.dumps(result, sort_keys=True), flush=True)
    return 0 if result['status'] == 'EXITED' and result['outer_exit_code'] == 0 else 1


if __name__ == '__main__':
    raise SystemExit(main())
