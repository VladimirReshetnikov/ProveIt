#!/usr/bin/env python3
"""Audit completed native child and failed enclosing no-alias endpoint run."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign25-generic-standard-retry-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign25-generic-standard-retry-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['outer_session_id'] == 28655 and outer['outer_exit_code'] == 1
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'FAILED' and state['failure'] == "RuntimeError('compile failed Sign25GenericStandardCurrent')"
assert state['runner_sha256'] == digest(packet / 'run.py') == '5c923b5f36b9d2b8393171941c8260a15acc604b720eea76ba31b0dab4fc8242'
assert [r['module'] for r in state['rows']] == ['Sign25GenericStandard', 'Sign25GenericStandardCurrent']
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
pins = {'Sign25DirectPolynomialBridge':'b662728032c262f52f1bda8a52d9b29401129c6279a3f9d4e6f8e2924980f1ea',
        'IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684',
        'IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19',
        'Sign25GenericStandard':'72ea694f8bcb2d8c4267dc6f38d79b274ddffde9a7de2c17d7c78a31009de3f4'}
guards = 0
for index, row in enumerate(state['rows']):
    name = row['module']
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == row['source_sha256'] == manifest[index]['source_sha256']
    assert digest(source) == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
    assert row['deps']['exit'] == 0 and row['compile']['exit'] == (0 if index == 0 else -6)
    for phase in ('deps', 'compile'):
        stage = row[phase]
        assert stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        log = name + '-' + phase + '.txt'
        assert digest(attempt / log) == digest(output / log) == stage['log_sha256']
    for path, observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else:
            assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
        guards += 1
    for mod in manifest[index]['imports']:
        dep = row['dependencies'][mod]
        assert dep['sha256'] == pins[mod.split('.')[-1]]
        assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'], 'realpath':dep['realpath']}
native = output / 'lib/DiophantineConsistency/Sign25GenericStandard.olean'
assert digest(native) == state['rows'][0]['object_sha256'] == pins['Sign25GenericStandard']
native_log = ' '.join((attempt / 'Sign25GenericStandard-compile.txt').read_text().split())
assert "'DiophantineConsistency.Sign25GenericStandard.standard_of_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]" in native_log
assert 'warning:' not in native_log and 'sorryAx' not in native_log and 'error:' not in native_log
log = (attempt / 'Sign25GenericStandardCurrent-compile.txt').read_text()
assert 'memory_exception' in log and "'interpreter'" in log
for name in ('Sign25GenericStandardCurrent', 'Sign25GenericStandardTranslated'):
    assert not (output / 'lib/DiophantineConsistency' / (name + '.olean')).exists()
for path, target in state['overlay_links'].items():
    assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent/check.py'
assert digest(upstream) == 'e355b74413e5748d74a78f1a365f9378fe04c5d7ba2e52668ccba96fa7e2c5bd'
subprocess.run([sys.executable, '-I', '-S', '-B', str(upstream)], check=True, capture_output=True, timeout=120)
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT', 'author_session':28655, 'author_outer_exit':1,
                  'native_compile_exit':0, 'standard_compile_exit':-6, 'guards':guards,
                  'overlay_links':len(state['overlay_links']), 'state_sha256':digest(state_path),
                  'scope':'generic standard child compiled; concrete specialization failed and no postflight'}, sort_keys=True, indent=2))
