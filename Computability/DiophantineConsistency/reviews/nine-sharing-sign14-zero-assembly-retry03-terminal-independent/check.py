#!/usr/bin/env python3
"""Audit successful sign20 zero assembly and providers."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign14-zero-assembly-retry03-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign14-zero-assembly-retry03-check-20261110')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 49192 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 2 and state['runner_sha256'] == digest(packet / 'run.py')
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
names = ['Sign14ForwardBridge','Sign14ReverseBridge']
objects = ['2d0b49f176234089742d278660eec2b4e10f47e1e4e4876c06e9d685207ac35f','7ea2b752484bef153bd60daa91fcf88abe9b31fea59cf4216e14068fdfbb1a61']
transfer_state=json.loads((root/'research/nine-sharing-sign14-transfers-check/attempt01/state.json').read_text())
assert transfer_state['status']=='PASS' and len(transfer_state['rows'])==5
pins={r['module']:r['object_sha256'] for r in transfer_state['rows']}
pins.update(dict(zip(names,objects)))
guards = 0
for row, entry, name, obj in zip(state['rows'], manifest, names, objects):
    assert row['module'] == name and entry['module'] == 'DiophantineConsistency.' + name
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == row['source_sha256'] == entry['source_sha256'] == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
    assert digest(output / 'lib/DiophantineConsistency' / (name + '.olean')) == row['object_sha256'] == obj
    for phase in ('deps','compile'):
        stage = row[phase]
        assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        log = name + '-' + phase + '.txt'
        assert digest(attempt / log) == digest(output / log) == stage['log_sha256'] == outer['logs'][log]
    for path, observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
        guards += 1
    for mod in entry['imports']:
        dep = row['dependencies'][mod]
        assert dep['sha256'] == pins[mod.split('.')[-1]]
        assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'], 'realpath':dep['realpath']}
    log = ' '.join((attempt / (name + '-compile.txt')).read_text().split())
    assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
    for th, axioms in ([('old_rows','[propext]'),('forward','[propext, Classical.choice, Quot.sound]')] if name == names[0] else [('new_rows','[propext]'),('backward','[propext, Classical.choice, Quot.sound]')]):
        assert "'DiophantineConsistency.Sign14ZeroBridge." + th + "' depends on axioms: " + axioms in log
for path, target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign14-transfers-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':49192,'stages':2,'guards':guards,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'pointwise signed-gap forward under supplied embedding and backward recovery seed zero maps; no iPRA endpoint'},sort_keys=True,indent=2))
