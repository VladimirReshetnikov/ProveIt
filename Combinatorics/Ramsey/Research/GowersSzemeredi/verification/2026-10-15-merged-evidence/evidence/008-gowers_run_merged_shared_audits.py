"""One guarded shared invocation of all57 roots on the actual merged source."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, signal, subprocess, sys, traceback
sys.dont_write_bytecode = True
if sys.flags.optimize: raise RuntimeError('Assertions must remain enabled')
BASE = Path('/tmp/gowers-merged-native-tools')
GUARD = BASE / 'guard.py'
GUARD_SHA = '59675ea063b9809e2f9db1bf541698bc67a3b75493d85ace82b3c92fc52d692f'
ATTEMPT_CHECKS = Path('/tmp/gowers-merged-shared-native-tools-v3/actual_attempt_checks.py')
ATTEMPT_CHECKS_SHA = '832e90738b753963b9ffa0d3fe6cf57ee7a9f52aedd01db2f3adbdd23982bb44'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def write_new(path, value):
    with path.open('x') as out:
        json.dump(value, out, indent=2); out.write('\n'); out.flush(); os.fsync(out.fileno())
    path.chmod(0o444)
def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--tools-review', type=Path, required=True); p.add_argument('--tools-review-sha256', required=True)
    p.add_argument('--core-receipt', type=Path, required=True); p.add_argument('--core-receipt-sha256', required=True)
    p.add_argument('--attempt-dir', type=Path, required=True); p.add_argument('--run', action='store_true'); a = p.parse_args()
    assert sha(GUARD) == GUARD_SHA and re.fullmatch('[0-9a-f]{64}', a.tools_review_sha256 or '') and sha(a.tools_review) == a.tools_review_sha256
    review = json.loads(a.tools_review.read_text()); ns = {'__file__': str(GUARD), '__name__': 'merged_guard_library'}
    exec(compile(GUARD.read_bytes(), str(GUARD), 'exec'), ns)
    snapshot = json.loads(ns['SNAPSHOT'].read_text()); runner_sha = sha(__file__); mode = snapshot['modes']['shared']; source_commit = snapshot['source_commit']
    assert review['status'].startswith('PASS') and review['findings'] == [] and 'shared' in review['approved_modes']
    assert review['snapshot_path'] == str(ns['SNAPSHOT']) and review['snapshot_sha256'] == ns['SNAPSHOT_SHA']
    assert review['guard_path'] == str(GUARD) and review['guard_sha256'] == GUARD_SHA
    assert review['runner_path'] == str(Path(__file__).resolve()) and review['runner_sha256'] == runner_sha
    assert re.fullmatch('[0-9a-f]{64}', a.core_receipt_sha256 or '') and sha(a.core_receipt) == a.core_receipt_sha256
    core = json.loads(a.core_receipt.read_text()); core_mode = snapshot['modes']['core']
    assert not (a.core_receipt.parent / 'failure-after-receipt.json').exists()
    assert core['status'] == 'passed' and core['validation_mode'] == 'core' and core['source_commit'] == source_commit
    assert type(core['terminal_exit']) is int and core['terminal_exit'] == 0
    assert core['terminal_module_count'] == core_mode['module_count'] and core['terminal_module_count_matches'] is True and core['contains_error_diagnostic'] is False
    assert core['snapshot_path'] == str(ns['SNAPSHOT']) and core['snapshot_sha256'] == ns['SNAPSHOT_SHA'] and core['source_guard_sha256'] == GUARD_SHA
    assert core['runner_sha256'] == 'fbec54638f6059d2eb8ee4174c101136f5b93385bc61ef9075a26b55b05bc9de'
    core_runner = BASE / 'gowers_run_merged_core_audits.py'; assert sha(core_runner) == core['runner_sha256']
    assert core['ordered_roots'] == core_mode['roots'] and core['command'][1:] == [ns['CHECKER'], *core_mode['roots']]
    assert core['source_guard_before'] == core['source_guard_after'] and core['source_and_evidence_stable'] is True and core['artifact_stability_verified'] is True
    assert len(core['artifacts_after']) == core_mode['module_count'] and set(core['artifacts_after']) == set(core_mode['modules'])
    assert core['native_source_repairs'] == snapshot['native_source_repairs'] and core['retained_historical_outcomes'] == 0
    core_log = Path(core['log']); assert sha(core_log) == core['log_sha256']; core_text = core_log.read_text()
    assert re.findall(r'^Checked (\d+) modules \(including up-to-date dependencies\)\.$', core_text, re.M) == [str(core_mode['module_count'])]
    assert core_text.rstrip().endswith(f"Checked {core_mode['module_count']} modules (including up-to-date dependencies).") and not ns['error_diagnostic'](core_text)
    assert sha(core['tools_review']) == core['tools_review_sha256']; core_review = json.loads(Path(core['tools_review']).read_text())
    assert core_review['status'].startswith('PASS') and core_review['findings'] == [] and 'core' in core_review['approved_modes']
    assert core_review['snapshot_sha256'] == ns['SNAPSHOT_SHA'] and core_review['guard_sha256'] == GUARD_SHA and core_review['runner_sha256'] == core['runner_sha256']
    assert ns['when'](core['finished_at']) <= ns['when'](core['final_evidence_checked_at']) <= ns['when'](now())
    assert sha(ATTEMPT_CHECKS) == ATTEMPT_CHECKS_SHA; checks = {}
    exec(compile(ATTEMPT_CHECKS.read_bytes(), str(ATTEMPT_CHECKS), 'exec'), checks)
    core_actual_pins = checks['validate_attempt'](a.core_receipt, core, snapshot, ns['ROOT'])
    before = ns['guard'](source_commit, 'shared'); idle = ns['worker_check']()
    artifacts_before = ns['artifact_snapshot']([mode['modules']], snapshot['graph'], require_fresh=False)
    executable = Path(sys.executable).resolve(strict=True); assert executable == Path('/proc/self/exe').resolve(strict=True)
    command = [sys.executable, ns['CHECKER'], *mode['roots']]; footer = f"Checked {mode['module_count']} modules (including up-to-date dependencies)."
    assert len(command) == 59 and len(mode['roots']) == 57
    tools = {str(GUARD): GUARD_SHA, str(Path(__file__).resolve()): runner_sha, str(a.tools_review.resolve()): a.tools_review_sha256, str(executable): sha(executable)}
    tools.update({str(a.core_receipt.resolve()): a.core_receipt_sha256, str(core_log): core['log_sha256'], core['tools_review']: core['tools_review_sha256'], str(core_runner): core['runner_sha256']})
    tools.update(core_actual_pins); tools[str(ATTEMPT_CHECKS)] = ATTEMPT_CHECKS_SHA
    tool_stamps = {p: ns['stamp'](p) for p in tools}
    def stable():
        ns['freeze_check'](before['source_freeze']); ns['freeze_check'](before['evidence_freeze']); ns['freeze_check'](tool_stamps)
        assert ns['head']() == source_commit
    if not a.run:
        print(json.dumps({'status': 'PASS: read-only preflight; native not started', 'mode': 'shared', 'source_commit': source_commit, 'command': command, 'expected_modules': mode['module_count'], 'protected_paths': before['protected_paths']}, indent=2)); return
    attempt = a.attempt_dir
    assert attempt.is_absolute() and attempt.resolve().is_relative_to(Path('/tmp')) and attempt.parent.is_dir() and not attempt.exists(), 'Preserve prior attempts; select a new directory'
    attempt.mkdir(exist_ok=False); log = attempt / 'native.log'; receipt = attempt / 'receipt.json'
    state = {'schema_version': 1, 'validation_mode': 'shared', 'status': 'running', 'source_commit': source_commit, 'core_receipt': {'path': str(a.core_receipt.resolve()), 'sha256': a.core_receipt_sha256}, 'core_attempt_evidence': core_actual_pins,
             'snapshot_path': str(ns['SNAPSHOT']), 'snapshot_sha256': ns['SNAPSHOT_SHA'], 'source_guard_sha256': GUARD_SHA, 'runner_sha256': runner_sha, 'tools_review': str(a.tools_review), 'tools_review_sha256': a.tools_review_sha256,
             'command': command, 'ordered_roots': mode['roots'], 'expected_modules': mode['module_count'], 'expected_inputs': mode['input_count'], 'expected_source_lines': mode['source_lines'],
             'started_at': now(), 'finished_at': None, 'terminal_exit': None, 'terminal_module_count': None, 'terminal_module_count_matches': False, 'contains_error_diagnostic': None,
             'log': str(log), 'log_sha256': None, 'source_guard_before': before, 'source_guard_after': None, 'workspace_worker_check': idle, 'preexisting_artifacts': artifacts_before,
             'artifacts_after': None, 'source_and_evidence_stable': False, 'artifact_stability_verified': False, 'native_source_repairs': snapshot['native_source_repairs'], 'failed_original_core': snapshot['failed_original_core'], 'retained_historical_outcomes': 0, 'per_root_native_outcomes_claimed': False}
    write_new(attempt / 'started.json', state); proc = None
    try:
        assert ns['guard'](source_commit, 'shared') == before; stable(); assert ns['worker_check']() == idle
        with log.open('x') as out:
            proc = subprocess.Popen(command, cwd=ns['ROOT'], stdout=out, stderr=subprocess.STDOUT, start_new_session=True)
            write_new(attempt / 'launched.json', {'pid': proc.pid, 'command': command, 'cwd': str(ns['ROOT']), 'observed_at': now()})
            while True:
                try: state['terminal_exit'] = proc.wait(timeout=1); break
                except subprocess.TimeoutExpired: stable(); ns['worker_check'](allowed_checker=proc.pid)
            out.flush(); os.fsync(out.fileno())
        state['finished_at'] = now(); text = log.read_text(); state['log_sha256'] = sha(log)
        footers = re.findall(r'^Checked (\d+) modules \(including up-to-date dependencies\)\.$', text, re.M)
        state['terminal_module_count'] = int(footers[0]) if len(footers) == 1 else None
        state['terminal_module_count_matches'] = footers == [str(mode['module_count'])] and text.rstrip().endswith(footer)
        state['contains_error_diagnostic'] = ns['error_diagnostic'](text)
        write_new(attempt / 'terminal.json', {k: state[k] for k in ('command', 'started_at', 'finished_at', 'terminal_exit', 'terminal_module_count', 'terminal_module_count_matches', 'contains_error_diagnostic', 'log', 'log_sha256')})
        assert type(state['terminal_exit']) is int and state['terminal_exit'] == 0 and state['terminal_module_count_matches'] and not state['contains_error_diagnostic']
        assert ns['worker_check']() == idle; stable(); state['source_guard_after'] = ns['guard'](source_commit, 'shared')
        state['source_and_evidence_stable'] = state['source_guard_after'] == before; assert state['source_and_evidence_stable']
        artifacts = ns['artifact_snapshot']([mode['modules']], snapshot['graph']); assert len(artifacts) == mode['module_count']
        assert ns['artifact_snapshot']([mode['modules']], snapshot['graph']) == artifacts
        for path, h in tools.items(): assert sha(path) == h
        assert sha(log) == state['log_sha256']; stable(); assert ns['worker_check']() == idle
        state.update(status='passed', artifacts_after=artifacts, artifact_stability_verified=True, final_evidence_checked_at=now()); write_new(receipt, state)
    except BaseException as exc:
        if proc is not None and proc.poll() is None:
            os.killpg(proc.pid, signal.SIGTERM)
            try: proc.wait(timeout=10)
            except subprocess.TimeoutExpired: os.killpg(proc.pid, signal.SIGKILL); proc.wait()
        state.update(status='failed', failure_type=type(exc).__name__, failure_detail=str(exc), failure_traceback=traceback.format_exc(), failure_recorded_at=now())
        if proc is not None and proc.poll() is not None: state['terminal_exit'] = proc.returncode
        state['finished_at'] = state['finished_at'] or now()
        if log.exists(): state['log_sha256'] = sha(log)
        write_new(receipt if not receipt.exists() else attempt / 'failure-after-receipt.json', state); raise
    finally:
        if log.exists(): log.chmod(0o444)
    print(json.dumps({'status': 'passed', 'mode': 'shared', 'receipt': str(receipt), 'receipt_sha256': sha(receipt), 'log': str(log), 'log_sha256': state['log_sha256'], 'terminal_exit': state['terminal_exit'], 'terminal_module_count': state['terminal_module_count']}, indent=2))
if __name__ == '__main__': main()
