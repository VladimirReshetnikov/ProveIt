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
packet = root / 'research/nine-sharing-sign19-coordinate-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign19-coordinate-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 16454 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1 and state['runner_sha256'] == digest(packet / 'run.py')
row, = state['rows']
name = 'Sign19Coordinate'
source = packet / 'src/DiophantineConsistency' / (name + '.lean')
manifest, = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert row['module'] == name and row['source_sha256'] == manifest['source_sha256'] == digest(source) == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
assert row['object_sha256'] == digest(output / 'lib/DiophantineConsistency' / (name + '.olean')) == '152766d2d71f8154b20dd8472afe13915c38b9e02c22824742a2e5d43e2fcab5'
for phase in ('deps', 'compile'):
    stage = row[phase]
    assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name + '-' + phase + '.txt'
    assert digest(attempt / log) == digest(output / log) == stage['log_sha256'] == outer['logs'][log]
for path, observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
pins = {'SharingSign19Squares':'e41498f629b5f0a3f84e5294b500cae65da0d5661d22a56734df9ec1d34cade2',
        'SharingSign20Squares':'214ceb97287c272b1ce00d079d0d9d930e7bb9d09d63438fd434e3b0680898dc'}
for mod in manifest['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]]
    assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'], 'realpath':dep['realpath']}
log = ' '.join((attempt / (name + '-compile.txt')).read_text().split())
assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for th in ('y_zero', 'y_coordinate', 'lift_drop'):
    assert ("'DiophantineConsistency.Sign19Coordinate." + th + "' depends on axioms: [propext, Classical.choice, Quot.sound]") in log
for path, target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign19-staged-syntax-terminal-independent', 'nine-sharing-sign20-seed-squares-terminal-independent'):
    subprocess.run([sys.executable, '-I', '-S', '-B', str(root / 'reviews' / review / 'check.py')], check=True, capture_output=True, timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT', 'author_session':16454, 'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']), 'state_sha256':digest(state_path),
                  'scope':'conditional Y lift and recovery with explicit hp0; no full model bridge'}, sort_keys=True, indent=2))
