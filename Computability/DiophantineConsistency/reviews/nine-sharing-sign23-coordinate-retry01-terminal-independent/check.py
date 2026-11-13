#!/usr/bin/env python3
"""Audit sign24 coordinate receipt and direct providers, without Lean."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign23-coordinate-retry01'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign23-coordinate-retry01-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 61340 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1 and state['runner_sha256'] == digest(packet / 'run.py')
row, = state['rows']
name = 'Sign23Coordinate'
source = packet / 'src/DiophantineConsistency' / (name + '.lean')
manifest, = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert row['module'] == name and row['source_sha256'] == manifest['source_sha256'] == digest(source) == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
assert row['object_sha256'] == digest(output / 'lib/DiophantineConsistency' / (name + '.olean')) == '483b0a5a095ea5660ad418d3d23bc63d392b84cf5742478f46f1dd7875bb31af'
for phase in ('deps', 'compile'):
    stage = row[phase]
    assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name + '-' + phase + '.txt'
    assert digest(attempt / log) == digest(output / log) == stage['log_sha256'] == outer['logs'][log]
for path, observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
pins = {'SharingSign23Squares':'54c3942898a68c560e8981d2932676030d88da0ad831775098a28d6e6bfc0aa2',
        'SharingSign24Squares':'fb25c2646953c4ae21c11d671b4ee62bf0ddc82a3c99fffb187b092b75f7e4ef'}
for mod in manifest['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]]
    assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'], 'realpath':dep['realpath']}
log = ' '.join((attempt / (name + '-compile.txt')).read_text().split())
assert log.count('warning:') == 1 and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.Sign23Coordinate.old_delta_row' depends on axioms: [propext]" in log
for th in ('delta_zero', 'delta_coordinate', 'lift_drop'):
    assert ("'DiophantineConsistency.Sign23Coordinate." + th + "' depends on axioms: [propext, Classical.choice, Quot.sound]") in log
for path, target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign24-seed-squares-terminal-independent', 'nine-sharing-sign23-seed-squares-terminal-independent'):
    subprocess.run([sys.executable, '-I', '-S', '-B', str(root / 'reviews' / review / 'check.py')], check=True, capture_output=True, timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT', 'author_session':61340, 'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']), 'state_sha256':digest(state_path),
                  'scope':'Delta lift and recovery; no full model bridge'}, sort_keys=True, indent=2))
