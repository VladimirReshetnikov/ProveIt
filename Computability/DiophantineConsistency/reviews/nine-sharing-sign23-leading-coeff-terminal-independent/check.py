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
packet = root/'research/nine-sharing-sign23-leading-coeff-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign23-leading-coeff-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session_id'] == 66649 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and 'failure' not in state
assert state['runner_sha256'] == digest(packet/'run.py') == '9d9bb109ccce88e94a968e13362ed1a04d4a5c631ca270905112f5ddb1b27699'
names = ['Sign23LeadingRows','Sign23DiagonalDegree','Sign23AxisResidualDegree','Sign23SquareCoeffs']
assert [r['module'] for r in state['rows']] == names
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
pins = {'Sign23CurrentExpressionDef':'2c80129f157842aac034a02199b437428b95e94150da0d2aec71fc1e00d93be0',
        'Sign23LeadingRows':'5642dc73d271bd573cafc9da593a7553a3c27e917b5bc1f7364fdc47d45173b3',
        'Sign23DiagonalDegree':'6247bb65a76e18def1ebfd4ca1d11ec5b795605acff4270f7506ca49bc430835',
        'Sign23AxisResidualDegree':'eac5e634e03dd4375bdb0e4ee7b6906887da736c3997ae37db2069072c928b11',
        'Sign23SquareCoeffs':'ba3dc7e04123f3022f11519361b082893824b2f80b05bcdd20c2ff6da3e9286d'}
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
    assert 'error:' not in log and 'sorryAx' not in log and 'warning:' not in log
    expected = [('n0_row','dc2_row','n0_axis','dc2_axis'), ('diagonal_totalDegree_le',), ('first_weighted_degree_le','other_weighted_degree_le','axisPoly_degree_le','axis_poly_degree_le'), ('n0_square_coeff','dc2_square_coeff')][i]
    for th in expected: assert "Sign23LeadingRows."+th+"' depends on axioms:" in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign23-concrete-polynomial-bridge-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':66649,'outer_exit':0,
                  'children':4,'guards':guards,'warnings':0,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'N0 and Dc2 coefficient one and remaining weighted degree ingredients; no full lower bound or external binding'},sort_keys=True,indent=2))
