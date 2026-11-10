#!/usr/bin/env python3
"""Audit failed wrapper run and inherited successful native child."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign25-endpoint-transfer-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign25-endpoint-transfer-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['outer_session_id'] == 76453 and outer['outer_exit_code'] == 1
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'FAILED' and state['failure'] == "RuntimeError('compile failed Sign25DirectNoAliasStandard')"
assert state['runner_sha256'] == digest(packet / 'run.py') == '8b2eaa1f44950c26e7d49357e80011b8900a7d7a979d094be5c429c51b1db2a8'
assert len(state['rows']) == 1
row, = state['rows']
name = 'Sign25DirectNoAliasStandard'
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert row['module'] == name and manifest[0]['module'] == 'DiophantineConsistency.' + name
source = packet / 'src/DiophantineConsistency' / (name + '.lean')
assert digest(source) == row['source_sha256'] == manifest[0]['source_sha256'] == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
assert row['deps']['exit'] == 0 and row['compile']['exit'] == -6
for phase in ('deps','compile'):
    stage = row[phase]
    assert stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name + '-' + phase + '.txt'
    assert digest(attempt / log) == digest(output / log) == stage['log_sha256']
log = (attempt / (name + '-compile.txt')).read_text()
assert 'memory_exception' in log and "'interpreter'" in log
for name in ('Sign25DirectNoAliasStandard','Sign25DirectNoAliasTranslated'):
    assert not (output / 'lib/DiophantineConsistency' / (name + '.olean')).exists()
pins = {'Sign25DirectNoAliasNative':'90c2795bbcca2630f16e1b0f0cb7ee7723a849c0a401bcf240115888faadcd8b',
        'IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19'}
for mod in manifest[0]['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]]
    assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
for path, observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
for path, target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign25-endpoint-no-alias-terminal-independent/check.py'
assert digest(upstream) == '3efa7f2442a8855d6f5b9df2ada203bd05b35de0eb162609bcbf4e80d268f6ac'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':76453,'author_outer_exit':1,
                  'standard_deps_exit':0,'standard_compile_exit':-6,'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'failed standard wrapper; native child inherited from failed parent'},sort_keys=True,indent=2))
