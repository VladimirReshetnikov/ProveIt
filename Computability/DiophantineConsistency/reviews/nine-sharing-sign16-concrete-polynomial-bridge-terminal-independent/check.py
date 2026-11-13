#!/usr/bin/env python3
"""Audit scoped -M3600 sign16 polynomial-bridge result and providers."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign16-concrete-polynomial-bridge-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign16-concrete-polynomial-bridge-check-20261110')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 12073 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1
assert state['runner_sha256'] == digest(packet/'run.py') == 'be719a413b3227a13a732ae7cc9b3dd3c0c59f94affaaa703adf935955bde5a4'
runner = (packet/'run.py').read_text()
assert "'-M3600'" in runner and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner
row, = state['rows']
name = 'Sign16DirectPolynomialBridge'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
src = packet/'src/DiophantineConsistency'/(name+'.lean')
assert row['module'] == name and row['source_sha256'] == entry['source_sha256'] == digest(src) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
assert digest(src) == '3687ae1a1478c904674d9db81df9759772dfffeb8288dfefbbcb49df6c6bd32c'
assert row['object_sha256'] == digest(output/'lib/DiophantineConsistency'/(name+'.olean')) == '267cb36d950cd00e3a6ceafc7df400b17b5e315375f17fe4477eeef008d8ec69'
for phase in ('deps','compile'):
    stage = row[phase]
    assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    assert stage['rss_limit_bytes'] == 4*1024**3 and stage['host_floor_bytes'] == 10*1024**3 and stage['timeout_seconds'] == 120
    log = name+'-'+phase+'.txt'
    assert digest(attempt/log) == digest(output/log) == stage['log_sha256'] == outer['logs'][log]
pins = {'Sign16ExpressionEquivalence':'d02a419606be4cc2e47fdd1dbff9af070f6f6b7eaeba0d58ec7c87e14201e35f',
        'GenericPolynomialBridgeTransport':'235092c6b941bffeb66e9d1f315e080436c7bc2e1fa77a5144e7889581b0895b',
        'Sign17DirectPolynomialBridge':'d161a98d5e26dcc66cbe035f2f744b7aa85c26f395ea6e8909455605ea591621'}
for mod in entry['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
log = ' '.join((attempt/(name+'-compile.txt')).read_text().split())
assert "'DiophantineConsistency.Sign16DirectIPRA.polynomialBridge' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
preflight = root/'reviews/nine-sharing-sign16-concrete-polynomial-bridge-prelaunch-independent/result.json'
assert json.loads(preflight.read_text())['status'] == 'PASS_PRELAUNCH'
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':12073,'outer_exit':0,'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'sign16 symbolic PolynomialBridge only; no iPRA endpoint or external file binding'},sort_keys=True,indent=2))
