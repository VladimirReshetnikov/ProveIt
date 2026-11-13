#!/usr/bin/env python3
"""Audit failed sign24 polynomial-bridge compile and direct observations."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign24-polynomial-bridge-bypass-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign24-polynomial-bridge-bypass-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 33816 and outer['author_observed_numeric_outer_exit'] == 1
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'FAILED' and state['failure'] == "RuntimeError('compile failed Sign24BypassPolynomialBridge')"
assert state['runner_sha256'] == digest(packet/'run.py') and len(state['rows']) == 1
row, = state['rows']
name = 'Sign24BypassPolynomialBridge'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
src = packet/'src/DiophantineConsistency'/(name+'.lean')
assert row['module'] == name and row['source_sha256'] == entry['source_sha256'] == digest(src) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
assert row['deps']['exit'] == 0 and row['compile']['exit'] == -6
for phase in ('deps','compile'):
    stage = row[phase]
    assert stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name+'-'+phase+'.txt'
    assert digest(attempt/log) == digest(output/log) == stage['log_sha256'] == outer['logs'][log]
log = (attempt/(name+'-compile.txt')).read_text()
assert 'memory_exception' in log and "'interpreter'" in log
assert not (output/'lib/DiophantineConsistency'/(name+'.olean')).exists()
pins = {'Sign24ExpressionEquivalence':'6eb1f0abfdf5adc4674e2dfb8a93265ac23b3c97447588afc0c60d7715ebfc4b',
        'GenericPolynomialBridgeTransport':'235092c6b941bffeb66e9d1f315e080436c7bc2e1fa77a5144e7889581b0895b',
        'Sign25ExpressionEquivalence':'37ed3cc6346eb68df0fb8d4bec90edd66801cb9ba61f25301811202e1c141683',
        'Sign26DirectPolynomialBridge':'6f528a24eb7309ad9cea14501f0160ea5c092d9b4c2bf6908a1e6b83aee2acc3'}
for mod in entry['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign24-expression-equivalence-terminal-independent','nine-sharing-generic-polynomial-bridge-transport-retry01-terminal-frontier-independent','nine-sharing-sign25-expression-equivalence-terminal-frontier-independent','nine-sharing-sign26-concrete-polynomial-bridge-terminal-frontier-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':33816,'outer_exit':1,'compile_exit':-6,
                  'guards':len(row['direct_guard']),'overlay_links':len(state['overlay_links']),
                  'state_sha256':digest(state_path),'scope':'failed sign24 bridge; no final postflight or endpoint'},sort_keys=True,indent=2))
