#!/usr/bin/env python3
"""Audit source-elaboration failure, including the printed sorryAx report."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign25-generic-standard-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign25-generic-standard-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session_id'] == 62301 and outer['outer_exit_code'] == 1
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'FAILED' and state['failure'] == "RuntimeError('compile failed Sign25GenericStandard')"
assert state['runner_sha256'] == digest(packet/'run.py') == '4f5f9d7b744fe0faf5f4c037e96f7e8579ec021b87d04b92b2f324d67a1fab1d'
row, = state['rows']
name = 'Sign25GenericStandard'
entry = json.loads((packet/'source-manifest.json').read_text())['rows'][0]
src = packet/'src/DiophantineConsistency'/(name+'.lean')
assert row['module'] == name and row['source_sha256'] == entry['source_sha256'] == digest(src) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
assert row['deps']['exit'] == 0 and row['compile']['exit'] == 1
for phase in ('deps','compile'):
    stage = row[phase]
    assert stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name+'-'+phase+'.txt'
    assert digest(attempt/log) == digest(output/log) == stage['log_sha256']
log = (attempt/(name+'-compile.txt')).read_text()
assert 'unknown namespace `AdaptiveEquationSyntax2011`' in log and 'Unknown identifier `mappedNativeRefutation`' in log
assert 'sorryAx' in log
for n in ('Sign25GenericStandard','Sign25GenericStandardCurrent','Sign25GenericStandardTranslated'):
    assert not (output/'lib/DiophantineConsistency'/(n+'.olean')).exists()
pins = {'IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684',
        'IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19'}
for mod in entry['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]]
    assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
for path, observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root/'reviews/nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':62301,'outer_exit':1,'compile_exit':1,
                  'sorryAx_in_failed_log':True,'state_sha256':digest(state_path),'guards':len(row['direct_guard']),
                  'scope':'failed elaboration only; no theorem object or later stages'},sort_keys=True,indent=2))
