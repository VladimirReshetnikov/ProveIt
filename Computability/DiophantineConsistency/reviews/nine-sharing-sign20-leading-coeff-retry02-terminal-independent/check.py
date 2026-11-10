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
packet = root/'research/nine-sharing-sign20-leading-coeff-retry02-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign20-leading-coeff-retry02-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session'] == 36539 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and 'failure' not in state
assert state['runner_sha256'] == digest(packet/'run.py') == 'df3a2c1aebe9b5510565b13a61152e00ea4d8c77fa448c33f8cb5cdc5b11ef05'
names = ['Sign20LeadingRows','Sign20DiagonalDegree','Sign20AxisResidualDegree','Sign20SquareCoeffs']
assert [r['module'] for r in state['rows']] == names
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
pins = {'Sign20CurrentExpressionDef':'325ed61a2f8d6f4af8516240f782f83d5ca83579c8184a7fad5dc066d02f96a3',
        'Sign20LeadingRows':'e0bc731ef4a159c19de95a68f1b4fd440ad4907d350de784bcccac3e2a095d27',
        'Sign20DiagonalDegree':'6f93b761be7a130a6e0609b24792219c5d63f4b859ac21dd1e22fc7c7bdf75af',
        'Sign20AxisResidualDegree':'1279f19aa65fbe14625aad3bcf61357a59529473e3ef313a1358a5ea50b2e487',
        'Sign20SquareCoeffs':'8a97ea9f9d11843a3815c44c162b29e953c91f6b5278d4cae5580bd941a3f188'}
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
    assert 'error:' not in log and 'sorryAx' not in log and log.count('warning:') == [1,0,6,0][i]
    expected = [('n0_row','dc2_row','n0_axis','dc2_axis'), ('diagonal_totalDegree_le',), ('first_weighted_degree_le','other_weighted_degree_le','axisPoly_degree_le','axis_poly_degree_le'), ('dc2_square_coeff','n0_square_coeff')][i]
    for th in expected: assert "Sign20LeadingRows."+th+"' depends on axioms:" in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':36539,'outer_exit':0,
                  'children':4,'guards':guards,'warnings':7,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'N0/Dc2 row-axis and separate z^4 square coefficient ingredients; no full lower bound or external binding'},sort_keys=True,indent=2))
