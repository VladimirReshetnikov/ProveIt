#!/usr/bin/env python3
"""Audit sign20 squares receipt and direct provider observations, no Lean."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign20-seed-squares-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign20-seed-squares-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 91776 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 2
assert state['runner_sha256'] == digest(packet / 'run.py') == 'd0d76c48899677cb8e5895c78cf1909a0b1f31bd248fd4af115c82c2b9a4ed75'
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
names = ['SharingSeed20Degree20', 'SharingSign20Squares']
objects = ['11e3586259007cc490b5485176b4faf271e55e827a1fa8613b286eb5bd3ce62e', '214ceb97287c272b1ce00d079d0d9d930e7bb9d09d63438fd434e3b0680898dc']
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
assert "'DiophantineConsistency.SharingSign20Squares.seed_zero_iff_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join((attempt / 'SharingSign20Squares-compile.txt').read_text().split())
for path, target in state['overlay_links'].items():
    assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign33-seed-squares-terminal-frontier-independent/check.py'
subprocess.run([sys.executable, '-I', '-S', '-B', str(upstream)], check=True, capture_output=True, timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT', 'author_session':91776, 'stages':2,
                  'guards':guards, 'overlay_links':len(state['overlay_links']),
                  'state_sha256':digest(state_path), 'scope':'symbolic seed zero iff residual zeros only'}, sort_keys=True, indent=2))
