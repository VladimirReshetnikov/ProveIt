#!/usr/bin/env python3
"""Audit generic structured-degree children and failed residual stage."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign24-degree-lower-retry-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign24-degree-lower-retry-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session_id'] == 2251 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and 'failure' not in state
assert state['runner_sha256'] == digest(packet/'run.py') == 'f4517edf0356737bc0a09294a20868f8be8eac8cf91bc574f6eb92f4cdc2c0fc'
names = ['Sign24LeadingN0','Sign24DiagonalDegree']
assert [r['module'] for r in state['rows']] == names
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
pins = {'Sign24CurrentExpressionDef':'c4461171b21c8317ec96470f066049d5d1457fcd934e71facadd2dd099e73f9f',
        'Sign24LeadingN0':'a7c39da23025abb0e9780e656f3a3fab7308afe611f3f6f06c5b74bfd7566eca',
        'Sign24DiagonalDegree':'43b85c01a0d23f87f1c3733a1cd73b1f01f1ea63ec7e11f4601fdf0937c724f1'}
guards = 0
for i,(row,entry,name) in enumerate(zip(state['rows'],manifest,names)):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert row['source_sha256'] == entry['source_sha256'] == digest(src) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
    assert row['deps']['exit'] == 0 and row['compile']['exit'] == 0
    for phase in ('deps','compile'):
        stage = row[phase]
        assert stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        log = name+'-'+phase+'.txt'
        assert digest(attempt/log) == digest(output/log) == stage['log_sha256']
    for path,observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
        guards += 1
    for mod in entry['imports']:
        dep = row['dependencies'][mod]
        assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
    log = ' '.join((attempt/(name+'-compile.txt')).read_text().split())
    assert row['object_sha256'] == digest(output/'lib/DiophantineConsistency'/(name+'.olean')) == pins[name]
    assert 'error:' not in log and 'sorryAx' not in log
    if i == 0:
        for th in ('n0_row','n0_axis'): assert "Sign24LeadingN0."+th+"' depends on axioms: [propext]" in log
    else: assert "Sign24LeadingN0.diagonal_totalDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
    assert 'warning:' not in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign24-concrete-bridge-memory-retry-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':2251,'outer_exit':0,
                  'children':2,'guards':guards,'warnings':0,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'N0 row and ring axis identity plus diagonal totalDegree nonincrease; no full lower bound or external binding'},sort_keys=True,indent=2))
