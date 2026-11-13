#!/usr/bin/env python3
"""Audit current-port sign20 seed equivalence and partial data provider."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign19-current-iff-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign19-current-iff-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 74922 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1 and state['runner_sha256'] == digest(packet / 'run.py')
row, = state['rows']
name = 'Sign19CurrentSeedIff'
source = packet / 'src/DiophantineConsistency' / (name + '.lean')
entry, = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert row['module'] == name and row['source_sha256'] == entry['source_sha256'] == digest(source) == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
assert row['object_sha256'] == digest(output / 'lib/DiophantineConsistency' / (name + '.olean')) == 'c08944762b4d6b4381b0029f85526367bd76418409e4bc8b88789ad3bbf2aeee'
for phase in ('deps','compile'):
    stage = row[phase]
    assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name + '-' + phase + '.txt'
    assert digest(attempt / log) == digest(output / log) == stage['log_sha256'] == outer['logs'][log]
for path, observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
pins = {'CurrentKernelData2011':'95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896',
        'Sign19SeedExistential':'c2410e7fb70bcad23ec2cdf7f915d2dfe017cf17412658d6f86a2a2904f10837'}
for mod in entry['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
log = ' '.join((attempt / (name + '-compile.txt')).read_text().split())
assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for th in ('port0','exists_same_input'):
    assert "'DiophantineConsistency.Sign19CurrentSeedIff."+th+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path, target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign19-seed-iff-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
survey = subprocess.run([sys.executable,'-I','-S','-B',str(packet / 'port-survey.py')],check=True,capture_output=True,text=True,timeout=120)
assert 'failed producer' in json.loads(survey.stdout)['scope']
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':74922,'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'current-port same-input seed iff, current data from observed children of FAILED provider'},sort_keys=True,indent=2))
