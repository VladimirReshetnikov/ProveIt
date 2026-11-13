#!/usr/bin/env python3
"""Audit sign24 squares receipt and direct provider observations, no Lean."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign23-seed-squares-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign23-seed-squares-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 85583 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 2
assert state['runner_sha256'] == digest(packet / 'run.py') == '644771a2b49b487103f352131431a5e4372f2a1a53456858d76546e3f33fbb58'
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
names = ['SharingSeed23Octic', 'SharingSign23Squares']
objects = ['0c75f19a212b499e902bab8e8a144ee51e5bb29124c0143f9f1a20453dbb48dc', '54c3942898a68c560e8981d2932676030d88da0ad831775098a28d6e6bfc0aa2']
pins = {'NineFreshJones':'9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df',
        'SharingSign33Squares':'48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42',
        **dict(zip(names, objects))}
guards = 0
for row, entry, name, obj in zip(state['rows'], manifest, names, objects):
    assert row['module'] == name and entry['module'] == 'DiophantineConsistency.' + name
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == row['source_sha256'] == entry['source_sha256'] == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
    assert digest(output / 'lib/DiophantineConsistency' / (name + '.olean')) == row['object_sha256'] == obj
    for phase in ('deps', 'compile'):
        stage = row[phase]
        assert stage['exit'] == 0 and stage['stop_reason'] is None
        assert not stage['monitor_errors'] and not stage['observed_descendant_pids']
        log = name + '-' + phase + '.txt'
        assert digest(attempt / log) == digest(output / log) == stage['log_sha256'] == outer['logs'][log]
    for path, observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else:
            assert candidate.is_file() and str(candidate.resolve()) == observation['realpath']
            assert digest(candidate) == observation['sha256']
        guards += 1
    for mod in entry['imports']:
        dep = row['dependencies'][mod]
        assert dep['sha256'] == pins[mod.split('.')[-1]]
        assert row['direct_guard'][dep['path']] == {'sha256': dep['sha256'], 'realpath': dep['realpath']}
    log = ' '.join((attempt / (name + '-compile.txt')).read_text().split())
    assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.SharingSign23Squares.seed_zero_iff_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join((attempt / 'SharingSign23Squares-compile.txt').read_text().split())
for path, target in state['overlay_links'].items():
    assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign33-seed-squares-terminal-frontier-independent/check.py'
subprocess.run([sys.executable, '-I', '-S', '-B', str(upstream)], check=True, capture_output=True, timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT', 'author_session':85583, 'stages':2,
                  'guards':guards, 'overlay_links':len(state['overlay_links']),
                  'state_sha256':digest(state_path), 'scope':'symbolic seed zero iff residual zeros only'}, sort_keys=True, indent=2))
