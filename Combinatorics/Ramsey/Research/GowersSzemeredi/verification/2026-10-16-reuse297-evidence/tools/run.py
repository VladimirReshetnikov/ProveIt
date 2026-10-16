"""Run exactly one pinned checker command, sequentially within a fresh batch."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse, fcntl, json, os, signal, subprocess, traceback
from common import *

def verify_prior(path, expected_hash, snapshot, snapshot_hash, label, guard):
    require(sha(path) == expected_hash, 'Prior receipt hash mismatch')
    receipt = json.loads(path.read_text()); spec = snapshot['modes'][label]
    require(receipt['status'] == 'passed' and receipt['mode'] == label, 'Prior mode did not pass')
    require(receipt['snapshot_sha256'] == snapshot_hash and receipt['source_commit'] == snapshot['source_commit'], 'Prior source mismatch')
    require(receipt['runner_sha256'] == sha(__file__), 'Prior runner mismatch')
    require(same(receipt['source_guard_before'], guard) and same(receipt['source_guard_after'], guard), 'Prior guard mismatch')
    started = json.loads((path.parent / 'started.json').read_text())
    require(same(started, {k: receipt[k] for k in started}) and set(started) == set(receipt['started_keys']), 'Started event mismatch')
    required_started = {'schema_version', 'mode', 'source_commit', 'snapshot_path', 'snapshot_sha256', 'runner_sha256', 'command', 'expected_modules', 'started_at', 'source_guard_before', 'previous_receipt'}
    require(set(started) == required_started, 'Started event keyset mismatch')
    launched = json.loads((path.parent / 'launched.json').read_text())
    require(set(launched) == {'pid', 'command', 'cwd', 'observed_at'} and type(launched['pid']) is int and launched['pid'] > 0, 'Launch event shape mismatch')
    require(same(launched, receipt['launched']) and launched['cwd'] == snapshot['root'] and same(launched['command'], receipt['command']), 'Launch event mismatch')
    require(receipt['command'][1:] == [CHECKER, *spec['roots']] and receipt['expected_modules'] == spec['module_count'], 'Prior command/count mismatch')
    terminal = terminal_fields(receipt['command'], receipt['started_at'], receipt['finished_at'], receipt['terminal_exit'], Path(receipt['log']), spec['module_count'])
    require(same(terminal, json.loads((path.parent / 'terminal.json').read_text())) and same(terminal, {k: receipt[k] for k in terminal}), 'Terminal/log mismatch')
    require(type(receipt['terminal_exit']) is int and receipt['terminal_exit'] == 0 and receipt['terminal_module_count_matches'] is True and receipt['contains_error_diagnostic'] is False, 'Prior native failure')
    require(receipt['artifact_stability_verified'] is True and receipt['source_stability_verified'] is True, 'Prior stability failure')
    times = [receipt['started_at'], launched['observed_at'], receipt['finished_at'], receipt['verified_at'], receipt['recorded_at']]
    times = [datetime.datetime.fromisoformat(value) for value in times]
    require(all(t.tzinfo is not None for t in times) and times == sorted(times), 'Prior event chronology mismatch')
    current = artifacts(snapshot, spec['cumulative_modules'], True)
    require(same(current, receipt['artifacts_after']), 'Prior artifacts changed')
    return receipt, {str(p): sha(p) for p in [path, path.parent / 'started.json', path.parent / 'launched.json', path.parent / 'terminal.json', Path(receipt['log'])]}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--snapshot', type=Path, required=True); p.add_argument('--snapshot-sha256', required=True)
    p.add_argument('--mode', choices=['core', 'shared', 'supplemental'], required=True)
    p.add_argument('--previous-receipt', type=Path); p.add_argument('--previous-receipt-sha256')
    p.add_argument('--attempt-dir', type=Path, required=True); p.add_argument('--run', action='store_true'); a = p.parse_args()
    require(sha(a.snapshot) == a.snapshot_sha256, 'Snapshot hash mismatch')
    snapshot = json.loads(a.snapshot.read_text()); root = Path(snapshot['root']); spec = snapshot['modes'][a.mode]
    base = Path(__file__).resolve().parent
    require(set(snapshot['tools']) == {str(base / n) for n in ('common.py', 'capture.py', 'run.py')}, 'Tool keyset mismatch')
    protected = dict(snapshot['tools']); protected[str(a.snapshot.resolve())] = a.snapshot_sha256
    protected[snapshot['plan']['path']] = snapshot['plan']['sha256']
    executable = Path(sys.executable).resolve(); protected[str(executable)] = sha(executable)
    require(executable == Path('/proc/self/exe').resolve(), 'Unexpected Python executable')
    for path, expected in protected.items(): require(sha(path) == expected, 'Tool/input hash mismatch: ' + path)
    guard = source_guard(snapshot); worker_check(root)
    prior = None; labels = list(snapshot['modes']); index = labels.index(a.mode)
    if index:
        require(a.previous_receipt is not None and a.previous_receipt_sha256 is not None, 'Immediate prior receipt required')
        prior, evidence = verify_prior(a.previous_receipt.resolve(), a.previous_receipt_sha256, snapshot, a.snapshot_sha256, labels[index - 1], guard)
        protected.update(evidence)
    else: require(a.previous_receipt is None and a.previous_receipt_sha256 is None, 'Core must start a fresh batch')
    files = [root / p for p in snapshot['source_hashes']] + [Path(p) for p in protected]
    stamps = {str(p): stamp(p) for p in files}
    def stable():
        require(head(root) == snapshot['source_commit'], 'HEAD changed during invocation')
        for path, expected in stamps.items(): require(stamp(path) == expected, 'Protected file changed: ' + path)
    command = [sys.executable, CHECKER, *spec['roots']]
    before_artifacts = artifacts(snapshot, spec['cumulative_modules'], False)
    if not a.run:
        stable(); print(json.dumps({'status': 'preflight passed; native not started', 'command': command, 'modules': spec['module_count']})); return
    attempt = a.attempt_dir
    require(attempt.is_absolute() and attempt.resolve().is_relative_to(Path('/tmp')) and attempt.parent.is_dir() and not attempt.exists(), 'Use a new /tmp attempt directory')
    lock_path = Path('/tmp') / ('gowers-native-' + hashlib.sha256(str(root).encode()).hexdigest()[:16] + '.lock')
    lock = lock_path.open('a'); fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    stable(); worker_check(root); attempt.mkdir(); log = attempt / 'native.log'
    state = {'schema_version': 1, 'mode': a.mode, 'source_commit': snapshot['source_commit'],
             'snapshot_path': str(a.snapshot.resolve()), 'snapshot_sha256': a.snapshot_sha256, 'runner_sha256': sha(__file__),
             'command': command, 'expected_modules': spec['module_count'], 'started_at': now(), 'source_guard_before': guard,
             'previous_receipt': None if prior is None else {'path': str(a.previous_receipt.resolve()), 'sha256': a.previous_receipt_sha256}}
    write_new(attempt / 'started.json', state); state['started_keys'] = list(state)
    state.update(status='running', terminal_exit=None, source_guard_after=None, artifacts_after=None, artifacts_before=before_artifacts,
                 source_stability_verified=False, artifact_stability_verified=False)
    proc = None; failure = None
    try:
        stable(); worker_check(root)
        with log.open('x') as output:
            proc = subprocess.Popen(command, cwd=root, stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
            state['launched'] = {'pid': proc.pid, 'command': command, 'cwd': str(root), 'observed_at': now()}
            write_new(attempt / 'launched.json', state['launched'])
            while True:
                try: state['terminal_exit'] = proc.wait(timeout=1); break
                except subprocess.TimeoutExpired: stable(); worker_check(root, proc.pid)
            output.flush(); os.fsync(output.fileno())
        state.update(terminal_fields(command, state['started_at'], now(), state['terminal_exit'], log, spec['module_count']))
        write_new(attempt / 'terminal.json', {k: state[k] for k in terminal_fields(command, state['started_at'], state['finished_at'], state['terminal_exit'], log, spec['module_count'])})
        require(type(state['terminal_exit']) is int and state['terminal_exit'] == 0 and state['terminal_module_count_matches'] and not state['contains_error_diagnostic'], 'Native command failed or footer/diagnostics invalid')
        worker_check(root); stable(); state['source_guard_after'] = source_guard(snapshot)
        require(same(state['source_guard_after'], guard), 'Post-source guard differs')
        state['source_stability_verified'] = True
        observed = artifacts(snapshot, spec['cumulative_modules'], True)
        if prior:
            require(all(same(observed[m], v) for m, v in prior['artifacts_after'].items()), 'Previously checked artifacts changed')
        require(same(observed, artifacts(snapshot, spec['cumulative_modules'], True)), 'Artifacts changed during stability check')
        for path, expected in protected.items(): require(sha(path) == expected, 'Protected evidence/tool changed')
        require(sha(log) == state['log_sha256'], 'Native log changed after terminal capture')
        stable(); worker_check(root)
        state.update(status='passed', artifacts_after=observed, artifact_stability_verified=True, verified_at=now())
    except BaseException as exc:
        failure = exc
        if proc is not None and proc.poll() is None:
            os.killpg(proc.pid, signal.SIGTERM)
            try: proc.wait(timeout=10)
            except subprocess.TimeoutExpired: os.killpg(proc.pid, signal.SIGKILL); proc.wait()
        state.update(status='failed', failure_type=type(exc).__name__, failure_detail=str(exc), failure_traceback=traceback.format_exc())
        if proc is not None:
            state.update(terminal_fields(command, state['started_at'], state.get('finished_at', now()), proc.returncode, log, spec['module_count']))
            if not (attempt / 'terminal.json').exists():
                write_new(attempt / 'terminal.json', {k: state[k] for k in terminal_fields(command, state['started_at'], state['finished_at'], proc.returncode, log, spec['module_count'])})
    finally:
        state['recorded_at'] = now(); write_new(attempt / 'receipt.json', state)
        if log.exists(): log.chmod(0o444)
    print(json.dumps({'status': state['status'], 'receipt': str(attempt / 'receipt.json'), 'receipt_sha256': sha(attempt / 'receipt.json'), 'terminal_exit': state['terminal_exit']}))
    if failure: raise failure
if __name__ == '__main__': main()
