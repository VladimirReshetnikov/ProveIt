#!/usr/bin/env python3
"""Audit completed import-only diagnostic and inherited partial provider."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign25-wrapper-import-diagnostic-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign25-wrapper-import-diagnostic-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['outer_session_id'] == 94228 and outer['outer_exit_code'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 3
assert state['runner_sha256'] == digest(packet / 'run.py') == '494fe3e9e62f725aea06438b5d12311b111c48721d2928e5fc1c098399167a82'
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
names = ['Sign25ImportNativeOnly','Sign25ImportStandardOnly','Sign25ImportBoth']
objects = ['fd61c83ca90d679c3915a7e7e20a73deba8ec556809197654bd8c60cba2a598f', '3441b307842129f2a3e403e8de3d81f48c6291cbfdb4a8ac008efa2c6c88a0f3', '4fb78a7c267b51a4691bcbf015aae29d3e64f3042b66f54eb11b102199d4fe5c']
pins = {'Sign25DirectNoAliasNative':'90c2795bbcca2630f16e1b0f0cb7ee7723a849c0a401bcf240115888faadcd8b',
        'IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19'}
guards = 0
for row, entry, name, obj in zip(state['rows'],manifest,names,objects):
    assert row['module'] == name and entry['module'] == 'DiophantineConsistency.'+name
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == row['source_sha256'] == entry['source_sha256'] == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
    assert digest(output / 'lib/DiophantineConsistency' / (name + '.olean')) == row['object_sha256'] == obj
    for phase in ('deps','compile'):
        stage = row[phase]
        assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        log = name + '-' + phase + '.txt'
        assert digest(attempt / log) == digest(output / log) == stage['log_sha256']
    assert not (attempt / (name+'-compile.txt')).read_text()
    for path, observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
        guards += 1
    for mod in entry['imports']:
        dep = row['dependencies'][mod]
        assert dep['sha256'] == pins[mod.split('.')[-1]]
        assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign25-endpoint-no-alias-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':94228,'stages':3,'guards':guards,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'import-only clients; prior native provider is successful child of FAILED outer run'},sort_keys=True,indent=2))
