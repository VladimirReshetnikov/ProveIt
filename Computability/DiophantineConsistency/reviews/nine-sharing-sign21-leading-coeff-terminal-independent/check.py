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
packet = root/'research/nine-sharing-sign21-leading-coeff-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign21-leading-coeff-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session'] == 82822 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and 'failure' not in state
assert state['runner_sha256'] == digest(packet/'run.py') == '94ec42b267bd9240a0658a61154a57d7635e766fc2585657d6d8d145cc47ea8e'
names = ['Sign21LeadingRow','Sign21DiagonalDegree','Sign21AxisResidualDegree']
assert [r['module'] for r in state['rows']] == names
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
pins = {'Sign21CurrentExpressionDef':'a8c661d9dd83991b57b0be84b013fee8c0a81b85f6a40981945c4693b9f8569e',
        'Sign21LeadingRow':'2a416d02774c3611e5f95855bb03df5070a8aa55be4d0574dd5ab445fb115afd',
        'Sign21DiagonalDegree':'99434b7106531f142f6ac5e972d71a5d917c89410324c747a45b2870c98bf78f',
        'Sign21AxisResidualDegree':'10e3a46fef42a19c7c81789695b10cca55fde29d82d5f04ec9842f162d4f2b11'}
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
    assert 'error:' not in log and 'sorryAx' not in log and log.count('warning:') == (9 if i == 2 else 0)
    expected = [('leading_row','leading_axis'), ('diagonal_totalDegree_le',), ('first_weighted_degree_le','other_weighted_degree_le','axisPoly_degree_le','axis_poly_degree_le')][i]
    for th in expected: assert "Sign21LeadingRow."+th+"' depends on axioms:" in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign21-concrete-polynomial-bridge-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':82822,'outer_exit':0,
                  'children':3,'guards':guards,'warnings':9,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'septic row-axis identity and remaining weighted degree ingredients; no full lower bound or external binding'},sort_keys=True,indent=2))
