#!/usr/bin/env python3
"""Audit sign23 Delta coordinate elaboration failure; no theorem claim."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign23-coordinate-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign23-coordinate-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 90674 and outer['author_observed_numeric_outer_exit'] == 1
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'FAILED' and state['failure'] == "RuntimeError('compile failed Sign23Coordinate')"
assert state['runner_sha256'] == digest(packet/'run.py') and len(state['rows']) == 1
row, = state['rows']
name = 'Sign23Coordinate'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
src = packet/'src/DiophantineConsistency'/(name+'.lean')
assert row['module'] == name and row['source_sha256'] == entry['source_sha256'] == digest(src) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
assert row['deps']['exit'] == 0 and row['compile']['exit'] == 1
for phase in ('deps','compile'):
    stage = row[phase]
    assert stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name+'-'+phase+'.txt'
    assert digest(attempt/log) == digest(output/log) == stage['log_sha256'] == outer['logs'][log]
log = (attempt/(name+'-compile.txt')).read_text()
assert 'error: unsolved goals' in log and 'ι 4' in log and 'ι 3' in log and 'sorryAx' in log
assert not (output/'lib/DiophantineConsistency'/(name+'.olean')).exists()
pins = {'SharingSign23Squares':'54c3942898a68c560e8981d2932676030d88da0ad831775098a28d6e6bfc0aa2',
        'SharingSign24Squares':'fb25c2646953c4ae21c11d671b4ee62bf0ddc82a3c99fffb187b092b75f7e4ef'}
for mod in entry['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign23-seed-squares-terminal-independent','nine-sharing-sign24-seed-squares-terminal-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':90674,'outer_exit':1,'compile_exit':1,
                  'sorryAx_in_failed_log':True,'guards':len(row['direct_guard']),'overlay_links':len(state['overlay_links']),
                  'state_sha256':digest(state_path),'scope':'failed numeral embedding simplification; no theorem object or postflight'},sort_keys=True,indent=2))
