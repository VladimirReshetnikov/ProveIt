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
packet = root/'research/nine-sharing-sign22-leading-coeff-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign22-leading-coeff-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session'] == 15223 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and 'failure' not in state
assert state['runner_sha256'] == digest(packet/'run.py') == '1aff0b38171289105f43ae2a74059f6c99ced4fcce1ba3216bee7e1fcafca0da'
names = ['Sign22LeadingRows','Sign22DiagonalDegree','Sign22AxisResidualDegree','Sign22SquareCoeffs']
assert [r['module'] for r in state['rows']] == names
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
pins = {'Sign22CurrentExpressionDef':'e6af82e204a6e942979ad67fd20fcdf27138f5b17143eeb3b65553d20bb2cb14',
        'Sign22LeadingRows':'5c68185d5dfdc8fd670b4526d99b540db422663b444e70ef656011ef16a01606',
        'Sign22DiagonalDegree':'6d5252b5716fa82cb4ca345a77ed4a502931eb6347fdc309716c0fc4e3adacb6',
        'Sign22AxisResidualDegree':'e1719e91836cac5dd6568cc375c0e035557219439a4a93d7f0a416249fac6766',
        'Sign22SquareCoeffs':'c696da1dc48f2721d938c81731642e4bb510e383b3e7a5f620c750def3955ebb'}
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
    assert 'error:' not in log and 'sorryAx' not in log and log.count('warning:') == (3 if i == 2 else 1 if i == 3 else 0)
    expected = [('n0_row','dc2_row','n0_axis','dc2_axis'), ('diagonal_totalDegree_le',), ('first_weighted_degree_le','other_weighted_degree_le','axisPoly_degree_le','axis_poly_degree_le'), ('dc2_square_coeff','n0_square_coeff')][i]
    for th in expected: assert "Sign22LeadingRows."+th+"' depends on axioms:" in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign22-concrete-polynomial-bridge-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':15223,'outer_exit':0,
                  'children':4,'guards':guards,'warnings':4,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'N0/Dc2 row-axis and separate 16/256 square coefficient ingredients; no full lower bound or external binding'},sort_keys=True,indent=2))
