#!/usr/bin/env python3
"""Audit sign20 seed iff receipt and direct providers, without Lean."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign18-seed-iff-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign18-seed-iff-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 71415 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1 and state['runner_sha256'] == digest(packet / 'run.py')
row, = state['rows']
name = 'Sign18SeedExistential'
source = packet / 'src/DiophantineConsistency' / (name + '.lean')
manifest, = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in source.read_text()
assert row['module'] == name and row['source_sha256'] == manifest['source_sha256'] == digest(source) == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
assert row['object_sha256'] == digest(output / 'lib/DiophantineConsistency' / (name + '.olean')) == '1e1057e13e103a8f1df3d7fdb94446b5d01d03397325dacb3b4ca061024f7e31'
for phase in ('deps', 'compile'):
    stage = row[phase]
    assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name + '-' + phase + '.txt'
    assert digest(attempt / log) == digest(output / log) == stage['log_sha256'] == outer['logs'][log]
for path, observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
pins = {'Sign18ReverseBridge':'899f43d1d6b7447be7c019eb9d8b779dc81f6e7b647922640d697a7adb49ce64'}
for mod in manifest['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]]
    assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'], 'realpath':dep['realpath']}
log = ' '.join((attempt / (name + '-compile.txt')).read_text().split())
assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for th in ('exists_same_input',):
    assert ("'DiophantineConsistency.Sign18SeedIff." + th + "' depends on axioms: [propext, Classical.choice, Quot.sound]") in log
for path, target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign18-zero-assembly-terminal-independent',):
    subprocess.run([sys.executable, '-I', '-S', '-B', str(root / 'reviews' / review / 'check.py')], check=True, capture_output=True, timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT', 'author_session':71415, 'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']), 'state_sha256':digest(state_path),
                  'scope':'same-input seed equivalence under explicit hp0; no endpoint'}, sort_keys=True, indent=2))
