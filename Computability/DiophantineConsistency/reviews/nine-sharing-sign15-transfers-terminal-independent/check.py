#!/usr/bin/env python3
"""Audit sign20 transfer artifacts and retained warning/axiom reports."""
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign15-transfers-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign15-transfers-check-20261110')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 53196 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 6 and state['runner_sha256'] == digest(packet / 'run.py')
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
objs = [r['object_sha256'] for r in state['rows']]
gates = [x['gate'] for x in json.loads((root/'research/nine-sharing-sign15-inner-candidate/seed.json').read_text())['residuals']]
assert len(objs)==len(gates)==6
guards = warnings = 0
for i, (row, entry, obj) in enumerate(zip(state['rows'], manifest, objs)):
    name = f'Sign15Transfer{i:02}'
    assert row['module'] == name and entry['module'] == 'DiophantineConsistency.' + name
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == row['source_sha256'] == entry['source_sha256'] == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
    assert digest(output / 'lib/DiophantineConsistency' / (name + '.olean')) == row['object_sha256'] == obj
    for phase in ('deps', 'compile'):
        stage = row[phase]
        assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        log = name + '-' + phase + '.txt'
        assert digest(attempt / log) == digest(output / log) == stage['log_sha256'] == outer['logs'][log]
    for path, observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
        guards += 1
    dep = row['dependencies']['DiophantineConsistency.Sign15Coordinate']
    assert dep['sha256'] == 'a4b7b88649794ca16095b680135372daa3dec0a58b3e46b174983769e7d2d077'
    assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'], 'realpath':dep['realpath']}
    log = (attempt / (name + '-compile.txt')).read_text()
    warnings += len(re.findall(r': warning:', log))
    assert 'error:' not in log and 'sorryAx' not in log
    normalized = ' '.join(log.split())
    for gate in gates[i:i+1]:
        assert ("'DiophantineConsistency.Sign15Transfers." + gate + "_eval' depends on axioms: [propext, Classical.choice, Quot.sound]") in normalized
assert warnings == 299
for path, target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign15-coordinate-terminal-independent/check.py'
subprocess.run([sys.executable, '-I', '-S', '-B', str(upstream)], check=True, capture_output=True, timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':53196,'stages':6,'guards':guards,
                  'overlay_links':len(state['overlay_links']),'warnings':warnings,'axiom_reports':6,
                  'state_sha256':digest(state_path),'scope':'6 residual evaluations under supplied signed-gap embedding; no assembled zero bridge'}, sort_keys=True, indent=2))
