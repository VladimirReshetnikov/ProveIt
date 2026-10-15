"""Read-only checks tying an actual successful attempt's files to its receipt."""
from pathlib import Path
import datetime, hashlib, json

def validate_attempt(receipt_path, receipt, snapshot, root):
    receipt_path = Path(receipt_path).resolve(); root = Path(root)
    assert receipt_path.name == 'receipt.json' and receipt['status'] == 'passed'
    assert Path(receipt['log']).resolve() == receipt_path.parent / 'native.log'
    assert not (receipt_path.parent / 'failure-after-receipt.json').exists()
    equal = lambda left, right: json.dumps(left, sort_keys=True) == json.dumps(right, sort_keys=True)
    guard = receipt['source_guard_before']
    assert equal(guard, receipt['source_guard_after'])
    assert set(guard) == {'snapshot_sha256', 'source_commit', 'mode', 'source_freeze', 'evidence_freeze', 'protected_paths', 'native_source_repairs'}
    assert guard['snapshot_sha256'] == receipt['snapshot_sha256']
    assert guard['source_commit'] == snapshot['source_commit'] == receipt['source_commit']
    assert guard['mode'] == receipt['validation_mode']
    assert guard['protected_paths'] == len(snapshot['protected_source_hashes'])
    assert guard['native_source_repairs'] == snapshot['native_source_repairs']
    assert set(guard['source_freeze']) == {str(root / p) for p in snapshot['protected_source_hashes']}
    assert set(guard['evidence_freeze']) == {receipt['snapshot_path'], snapshot['historical_roots_source']['path'], snapshot['failed_original_core']['path']}
    for stamps in (guard['source_freeze'], guard['evidence_freeze']):
        assert all(isinstance(s, list) and len(s) == 5 and all(type(x) is int and x >= 0 for x in s) for s in stamps.values())
    pins = {}
    def read(name):
        path = receipt_path.parent / name; data = path.read_bytes()
        pins[str(path)] = hashlib.sha256(data).hexdigest(); return json.loads(data)
    started = read('started.json'); launched = read('launched.json'); terminal = read('terminal.json')
    expected = dict(receipt); expected.pop('final_evidence_checked_at')
    expected.update(status='running', finished_at=None, terminal_exit=None, terminal_module_count=None,
                    terminal_module_count_matches=False, contains_error_diagnostic=None, log_sha256=None,
                    source_guard_after=None, artifacts_after=None, source_and_evidence_stable=False,
                    artifact_stability_verified=False)
    assert equal(started, expected)
    fields = ('command', 'started_at', 'finished_at', 'terminal_exit', 'terminal_module_count',
              'terminal_module_count_matches', 'contains_error_diagnostic', 'log', 'log_sha256')
    assert equal(terminal, {k: receipt[k] for k in fields})
    assert set(launched) == {'pid', 'command', 'cwd', 'observed_at'}
    assert type(launched['pid']) is int and launched['pid'] > 0
    assert launched['command'] == receipt['command'] and launched['cwd'] == str(root)
    def when(value):
        stamp = datetime.datetime.fromisoformat(value); assert stamp.tzinfo is not None; return stamp
    assert when(receipt['started_at']) <= when(launched['observed_at']) <= when(receipt['finished_at']) <= when(receipt['final_evidence_checked_at'])
    return pins
