#!/usr/bin/env python3
"""Audit sign20 coordinate receipt and direct providers, without Lean."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign17-coordinate-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign17-coordinate-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 63210 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1 and state['runner_sha256'] == digest(packet / 'run.py')
row, = state['rows']
name = 'Sign17Coordinate'
source = packet / 'src/DiophantineConsistency' / (name + '.lean')
manifest, = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert row['module'] == name and row['source_sha256'] == manifest['source_sha256'] == digest(source) == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
assert row['object_sha256'] == digest(output / 'lib/DiophantineConsistency' / (name + '.olean')) == 'cd6339950da27cac90bb31908662479e60497bd7ec074840edfd029bdc23f038'
for phase in ('deps', 'compile'):
    stage = row[phase]
    assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name + '-' + phase + '.txt'
    assert digest(attempt / log) == digest(output / log) == stage['log_sha256'] == outer['logs'][log]
for path, observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
pins = {'SharingSign17Squares':'51f81afaba554534380a855369a46664e7897e9c89f1335c02e3704ccfd90be2',
        'SharingSign18Squares':'7bc43d3507686e928fcd5fc61f79ce8081ec587551aff97f59ec61a90e90e30c'}
for mod in manifest['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]]
    assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'], 'realpath':dep['realpath']}
log = ' '.join((attempt / (name + '-compile.txt')).read_text().split())
assert log.count('warning:') == 2 and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.Sign17Coordinate.old_d_row' depends on axioms: [propext]" in log
for th in ('d_zero', 'old_gap', 'lift_drop'):
    assert ("'DiophantineConsistency.Sign17Coordinate." + th + "' depends on axioms: [propext, Classical.choice, Quot.sound]") in log
for path, target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign17-staged-syntax-terminal-independent', 'nine-sharing-sign18-staged-syntax-terminal-independent'):
    subprocess.run([sys.executable, '-I', '-S', '-B', str(root / 'reviews' / review / 'check.py')], check=True, capture_output=True, timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT', 'author_session':63210, 'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']), 'state_sha256':digest(state_path),
                  'scope':'conditional signed gap lift with supplied embedding; no gap existence or full model bridge'}, sort_keys=True, indent=2))
