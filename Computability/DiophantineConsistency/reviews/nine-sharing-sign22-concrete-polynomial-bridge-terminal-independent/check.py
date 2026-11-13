#!/usr/bin/env python3
"""Audit scoped -M3600 sign22 polynomial-bridge result and providers."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign22-concrete-polynomial-bridge-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign22-concrete-polynomial-bridge-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 14594 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1
assert state['runner_sha256'] == digest(packet/'run.py') == 'be500d8ed38de9b031261c57624f24287b388ef01fcb40a7fa2b9f81df3e65fc'
runner = (packet/'run.py').read_text()
assert "'-M3600'" in runner and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner
row, = state['rows']
name = 'Sign22DirectPolynomialBridge'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
src = packet/'src/DiophantineConsistency'/(name+'.lean')
assert row['module'] == name and row['source_sha256'] == entry['source_sha256'] == digest(src) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
assert digest(src) == '166f7117676882ee6531c4e371e70ba3c99513a0a3d08c525c36a3c564a10e53'
assert row['object_sha256'] == digest(output/'lib/DiophantineConsistency'/(name+'.olean')) == '53e98c8448caeebd9564037973e0ecd88be1793abd03f321d4d161f0651c7934'
for phase in ('deps','compile'):
    stage = row[phase]
    assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    assert stage['rss_limit_bytes'] == 4*1024**3 and stage['host_floor_bytes'] == 10*1024**3 and stage['timeout_seconds'] == 120
    log = name+'-'+phase+'.txt'
    assert digest(attempt/log) == digest(output/log) == stage['log_sha256'] == outer['logs'][log]
pins = {'Sign22ExpressionEquivalence':'bf581014465ad1e6f480d50a4cae33570fbf83ca7be2de7dc1452d8e14eef1e3',
        'GenericPolynomialBridgeTransport':'235092c6b941bffeb66e9d1f315e080436c7bc2e1fa77a5144e7889581b0895b',
        'Sign23DirectPolynomialBridge':'2cb1f6c016b2d608ecc59ff59c9d88be2ab5a19d76a65d4c98c9f1ed76360c71'}
for mod in entry['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
log = ' '.join((attempt/(name+'-compile.txt')).read_text().split())
assert "'DiophantineConsistency.Sign22DirectIPRA.polynomialBridge' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign22-expression-equivalence-terminal-independent','nine-sharing-generic-polynomial-bridge-transport-retry01-terminal-frontier-independent','nine-sharing-sign23-concrete-polynomial-bridge-terminal-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':14594,'outer_exit':0,'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'sign22 symbolic PolynomialBridge only; no iPRA endpoint or external file binding'},sort_keys=True,indent=2))
