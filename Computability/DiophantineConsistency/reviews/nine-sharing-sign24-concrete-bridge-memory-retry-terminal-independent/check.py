#!/usr/bin/env python3
"""Audit scoped -M3600 sign24 polynomial-bridge result and providers."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign24-concrete-bridge-memory-retry-check'
prior = root/'research/nine-sharing-sign24-concrete-polynomial-bridge-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign24-concrete-bridge-memory-retry-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session_id'] == 31996 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1
assert state['runner_sha256'] == digest(packet/'run.py') == 'b35611bbc283834f6c0ab17338385a1bc31ff30d30ae5609ab382b489df443a4'
runner = (packet/'run.py').read_text()
assert "'-M3600'" in runner and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner
row, = state['rows']
name = 'Sign24DirectPolynomialBridge'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
src = packet/'src/DiophantineConsistency'/(name+'.lean')
assert row['module'] == name and row['source_sha256'] == entry['source_sha256'] == digest(src) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
assert digest(src) == digest(prior/'src/DiophantineConsistency'/(name+'.lean'))
assert row['object_sha256'] == digest(output/'lib/DiophantineConsistency'/(name+'.olean')) == '7f868da1803547aaca112e044ec2f0ca8351599f0dbfe472b9a6ffc88621fe63'
for phase in ('deps','compile'):
    stage = row[phase]
    assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    assert stage['rss_limit_bytes'] == 4*1024**3 and stage['host_floor_bytes'] == 10*1024**3 and stage['timeout_seconds'] == 120
    log = name+'-'+phase+'.txt'
    assert digest(attempt/log) == digest(output/log) == stage['log_sha256']
pins = {'Sign24ExpressionEquivalence':'6eb1f0abfdf5adc4674e2dfb8a93265ac23b3c97447588afc0c60d7715ebfc4b',
        'GenericPolynomialBridgeTransport':'235092c6b941bffeb66e9d1f315e080436c7bc2e1fa77a5144e7889581b0895b',
        'Sign25DirectPolynomialBridge':'b662728032c262f52f1bda8a52d9b29401129c6279a3f9d4e6f8e2924980f1ea'}
for mod in entry['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
log = ' '.join((attempt/(name+'-compile.txt')).read_text().split())
assert "'DiophantineConsistency.Sign24DirectIPRA.polynomialBridge' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign24-expression-equivalence-terminal-independent','nine-sharing-generic-polynomial-bridge-transport-retry01-terminal-frontier-independent','nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':31996,'outer_exit':0,'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'sign24 symbolic PolynomialBridge only; no iPRA endpoint or external file binding'},sort_keys=True,indent=2))
