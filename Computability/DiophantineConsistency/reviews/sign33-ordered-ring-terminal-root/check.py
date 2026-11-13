import hashlib
import json
import os
from pathlib import Path

review = Path(__file__).resolve().parent
root = review.parents[1]
packet = root / 'research/sign33-ordered-ring-standalone-check'
attempt = packet / 'attempt01'
live = Path('/tmp/sign33-ordered-ring-standalone-check-20261106')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(attempt / 'state.json') == 'e6f245013055355451ee1411f0a5eed07e5815579a7741e2fddbb3f64446965a' == sha(live / 'state.json')
assert sha(attempt / 'outer-terminal-author-record.json') == '89c5154deb464246fb078aec41d64fb3ec3f1dac921c5f033aa853a84570e88c'
outer = json.loads((attempt / 'outer-terminal-author-record.json').read_text())
assert outer['outer_session_id'] == 22186 and outer['outer_exit_code'] == 0 and outer['runner_status'] == 'PASS'
state = json.loads((attempt / 'state.json').read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1
row = state['rows'][0]
assert row['module'] == 'Sign33OrderedRing'
assert row['source_sha256'] == sha(packet / 'src/Sign33OrderedRing.lean') == sha(live / 'src/Sign33OrderedRing.lean')
assert row['object_sha256'] == '04d0c914a6810e0e449d661e678a20422e500a6cc44e8467b50a2f30e3358c5a' == sha(live / 'lib/Sign33OrderedRing.olean')
for phase in ('deps', 'compile'):
    run = row[phase]
    name = 'Sign33OrderedRing-' + phase + '.txt'
    assert run['exit'] == 0 and run['stop_reason'] is None
    assert not run['monitor_errors'] and not run['observed_descendant_pids']
    assert run['log_sha256'] == sha(attempt / name) == sha(live / name)
assert row['compile']['log_sha256'] == 'f9ccc547cb57a43cf0f4b8b2607610ae3826a9bfe66b71f63547e5535b7cae9e'
log = (attempt / 'Sign33OrderedRing-compile.txt').read_text()
for theorem in ('gap_tau_signs', 'inner_V_signs', 'auxiliary_difference_sign'):
    assert "'Sign33OrderedRing." + theorem + "' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
assert len(state['direct_guard']) == 60
for name, record in state['direct_guard'].items():
    path = Path(name)
    if record is None:
        assert not os.path.lexists(path)
    else:
        assert path.is_file() and str(path.resolve()) == record['realpath'] and sha(path) == record['sha256']
for dep in row['dependencies'].values():
    record = state['direct_guard'][dep['path']]
    assert record == {'realpath': dep['realpath'], 'sha256': dep['sha256']}
print(json.dumps({'status': 'PASS_TERMINAL_AUDIT', 'scope': 'Recorded conditional ordered-ring theorems; no model bridge or Lean replay.'}, sort_keys=True))
