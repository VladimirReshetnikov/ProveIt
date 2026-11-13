#!/usr/bin/env python3
"""Audit sign24 staged bridge's conditional child and failed instantiation."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign24-polynomial-bridge-staged-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign24-polynomial-bridge-staged-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 97690 and outer['author_observed_numeric_outer_exit'] == 1
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'FAILED' and state['failure'] == "RuntimeError('compile failed Sign24BridgeStaged')"
assert len(state['rows']) == 2 and state['runner_sha256'] == digest(packet/'run.py')
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
names = ['Sign24BridgeConditional','Sign24BridgeStaged']
assert [r['module'] for r in state['rows']] == names
pins = {'GenericPolynomialBridgeTransport':'235092c6b941bffeb66e9d1f315e080436c7bc2e1fa77a5144e7889581b0895b',
        'Sign24ExpressionEquivalence':'6eb1f0abfdf5adc4674e2dfb8a93265ac23b3c97447588afc0c60d7715ebfc4b',
        'Sign25DirectPolynomialBridge':'b662728032c262f52f1bda8a52d9b29401129c6279a3f9d4e6f8e2924980f1ea',
        'Sign24BridgeConditional':'4a93a6f3d5466e118cb015b9236ca5df9cce1b92e1a344b7cff7651dbc6bc2dc'}
guards = 0
for i,(row,entry,name) in enumerate(zip(state['rows'],manifest,names)):
    source = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(source) == row['source_sha256'] == entry['source_sha256'] == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
    assert row['deps']['exit'] == 0 and row['compile']['exit'] == (0 if i == 0 else -6)
    for phase in ('deps','compile'):
        stage = row[phase]
        assert stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        log = name+'-'+phase+'.txt'
        assert digest(attempt/log) == digest(output/log) == stage['log_sha256'] == outer['logs'][log]
    for path,observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
        guards += 1
    for mod in entry['imports']:
        dep = row['dependencies'][mod]
        assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
    log = ' '.join((attempt/(name+'-compile.txt')).read_text().split())
    if i == 0:
        assert row['object_sha256'] == digest(output/'lib/DiophantineConsistency'/(name+'.olean')) == pins[name]
        assert "'DiophantineConsistency.Sign24StagedIPRA.transfer_from_sign25' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
        assert 'warning:' not in log and 'sorryAx' not in log
    else:
        assert 'memory_exception' in log and "'interpreter'" in log
        assert not (output/'lib/DiophantineConsistency'/(name+'.olean')).exists()
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign24-expression-equivalence-terminal-independent','nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT','author_session':97690,'outer_exit':1,'conditional_compile_exit':0,
                  'instantiation_compile_exit':-6,'guards':guards,'overlay_links':len(state['overlay_links']),
                  'state_sha256':digest(state_path),'scope':'conditional bridge child only; no unconditional bridge or final postflight'},sort_keys=True,indent=2))
