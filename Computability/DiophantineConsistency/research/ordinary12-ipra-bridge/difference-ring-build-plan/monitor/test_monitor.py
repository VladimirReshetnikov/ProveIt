#!/usr/bin/env python3
"""Isolated toy controls, using fake readings only through the imported API."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
from unittest.mock import patch

import monitor

BOOT="import runpy,sys; from pathlib import Path; p=Path(sys.argv[1]).resolve(strict=True); sys.path.insert(0,str(p.parent)); sys.argv=sys.argv[1:]; runpy.run_path(str(p),run_name='__main__')"
def isolated(script):return [sys.executable,'-I','-S','-c',BOOT,str(script)]


def dead_or_zombie(pid):
    path = Path(f'/proc/{pid}/stat')
    try:
        return path.read_text().split(') ', 1)[1].split()[0] == 'Z'
    except (FileNotFoundError, ProcessLookupError):
        # Reaping can surface as ENOENT or ESRCH while reading procfs.
        return True


def wait_dead(pid):
    for _ in range(100):
        if dead_or_zombie(pid):
            return
        time.sleep(.02)
    raise AssertionError(('descendant remains live', pid))


CHILD = r'''
import os,pathlib,signal,subprocess,sys,time
out=pathlib.Path(os.environ['MONITOR_OUTPUT']); out.mkdir()
signal.signal(signal.SIGTERM,signal.SIG_IGN)
child=subprocess.Popen([sys.executable,'-c','import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(60)'])
(out/'parent').write_text(str(os.getpid())); (out/'child').write_text(str(child.pid))
print('READY',flush=True)
while True: time.sleep(.1)
'''


def exercise_violation(root, reason):
    run = root / reason
    calls = 0
    def sensor():
        nonlocal calls
        calls += 1
        ready = (run/'child-output/parent').exists() and (run/'child-output/child').exists()
        if ready:
            return (99, 0) if reason == 'disk' else (1000, 101)
        return 1000, 0
    r = monitor.run(run, [sys.executable, '-c', CHILD], reserve=100, budget=100,
                    interval=.02, grace=.1, sensor=sensor)
    assert r['status'] == 'STOPPED'
    assert r['violation'] == ('free_space_below_sampled_threshold' if reason == 'disk' else 'logical_size_above_sampled_budget')
    assert r['outer_exit_code'] is not None and calls > 1
    child = int((run/'child-output/child').read_text())
    wait_dead(child)
    assert json.loads((run/'terminal.json').read_text())['outer_exit_code'] == r['outer_exit_code']
    print('PASS', reason, 'process group terminated', flush=True)


def main():
    for error in (FileNotFoundError, ProcessLookupError):
        with patch.object(Path, 'read_text', side_effect=error):
            assert dead_or_zombie(12345)
    print('PASS reaped procfs ENOENT and ESRCH controls', flush=True)
    with tempfile.TemporaryDirectory(prefix='ipra-monitor-tests-') as tmp:
        root = Path(tmp)
        command = [sys.executable, '-c', "import os,pathlib; p=pathlib.Path(os.environ['MONITOR_OUTPUT']); p.mkdir(); (p/'toy').write_text('ok'); (pathlib.Path(os.environ['TMPDIR'])/'toy').write_text('tmp'); print('TOY_OK')"]
        ok = monitor.run(root/'success', command, reserve=0, budget=1024*1024, interval=.02, grace=.1)
        assert ok['status'] == 'EXITED' and ok['outer_exit_code'] == 0
        assert (root/'success/child.log').read_text().strip() == 'TOY_OK'
        assert (root/'success/child-output/toy').read_text() == 'ok'
        assert (root/'success/tmp/toy').read_text() == 'tmp'
        try:
            monitor.run(root/'success', command, reserve=0, budget=100)
        except (FileExistsError, ValueError):
            pass
        else:
            raise AssertionError('existing run directory accepted')
        print('PASS actual success and fresh-path guard', flush=True)
        protected = root/'protected'; protected.mkdir()
        link = root/'link'; link.symlink_to(protected, target_is_directory=True)
        for destination in (protected/'new', link/'new'):
            result = subprocess.run(isolated(Path(monitor.__file__))+[
                '--run-dir', str(destination), '--protect', str(protected),
                '--reserve-bytes', '0', '--', sys.executable, '-c', 'pass'],
                text=True,capture_output=True)
            assert result.returncode != 0 and not (protected/'new').exists()
        inferred=protected/'inferred'
        result=subprocess.run(isolated(Path(monitor.__file__))+['--run-dir',str(inferred),
            '--reserve-bytes','0','--',sys.executable,'-c','pass','--snapshot',str(protected)],
            text=True,capture_output=True)
        assert result.returncode != 0 and not inferred.exists()
        optimized = root/'optimized'
        env = os.environ.copy(); env['PYTHONOPTIMIZE']='1'
        result = subprocess.run(isolated(Path(monitor.__file__))+[
            '--run-dir', str(optimized), '--reserve-bytes', '0', '--',
            sys.executable, '-c', 'pass'],env=env,text=True,capture_output=True)
        assert result.returncode != 0 and not optimized.exists() and 'rejects optimized' in result.stderr
        print('PASS protected paths, symlink ancestor and optimized CLI rejected before writes', flush=True)
        before = monitor.run(root/'preflight', command, reserve=100, budget=100,
                             sensor=lambda:(99,0))
        assert before['status'] == 'STOPPED_BEFORE_LAUNCH' and not (root/'preflight/child-output').exists()
        print('PASS preflight stop', flush=True)
        exercise_violation(root, 'disk')
        exercise_violation(root, 'budget')
        lingering_child = r'''
import os,pathlib,subprocess,sys,time
out=pathlib.Path(os.environ['MONITOR_OUTPUT']);out.mkdir()
script='import os,pathlib,signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); pathlib.Path(os.environ["MONITOR_OUTPUT"],"child").write_text(str(os.getpid())); time.sleep(60)'
subprocess.Popen([sys.executable,'-c',script])
while not (out/'child').exists(): time.sleep(.01)
'''
        lingering = monitor.run(root/'lingering', [sys.executable,'-c',lingering_child],
                                reserve=0,budget=1024*1024,interval=.02,grace=.1)
        assert lingering['status'] == 'STOPPED' and lingering['violation'] == 'lingering_process_group'
        assert lingering['outer_exit_code'] == 0
        wait_dead(int((root/'lingering/child-output/child').read_text()))
        print('PASS successful leader with lingering descendant rejected', flush=True)
        interrupt = root/'interrupt'
        cli = subprocess.Popen(isolated(Path(monitor.__file__))+[ '--run-dir', str(interrupt),
                                '--reserve-bytes', '0', '--interval', '.02', '--grace', '.1', '--', sys.executable, '-c', CHILD],
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        deadline = time.monotonic()+10
        while not (interrupt/'child-output/child').exists() and time.monotonic()<deadline:
            time.sleep(.02)
        assert (interrupt/'child-output/child').exists()
        child = int((interrupt/'child-output/child').read_text())
        cli.send_signal(signal.SIGTERM)
        out, err = cli.communicate(timeout=10)
        assert cli.returncode == 1 and not err
        record = json.loads((interrupt/'terminal.json').read_text())
        assert record['status'] == 'STOPPED' and record['violation'] == 'interrupt_signal_15'
        assert json.loads(out)['outer_exit_code'] == record['outer_exit_code']
        wait_dead(child)
        print('PASS actual interrupt and descendant cleanup', flush=True)
    print('PASS_MONITOR_TOY_CONTROLS', flush=True)

if __name__ == '__main__':
    main()
