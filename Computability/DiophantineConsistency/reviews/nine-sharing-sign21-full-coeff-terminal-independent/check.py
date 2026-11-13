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
packet = root/'research/nine-sharing-sign21-full-coeff-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign21-full-coeff-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session'] == 89132 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and 'failure' not in state
assert state['runner_sha256'] == digest(packet/'run.py') == '46dbe0051fdb6bda92f643ce122bc5985736c874fdb9d2c579004b0d8591beab'
names = ['Sign21LeadingRow','Sign21DiagonalDegree','Sign21AxisResidualDegree','Sign21SquareCoeff','Sign21AxisCoeffLemmas','Sign21SeedCoefficient','Sign21DegreeLower']
assert [r['module'] for r in state['rows']] == names
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
pins = {'Sign21CurrentExpressionDef':'a8c661d9dd83991b57b0be84b013fee8c0a81b85f6a40981945c4693b9f8569e',
'Sign21LeadingRow':'2a416d02774c3611e5f95855bb03df5070a8aa55be4d0574dd5ab445fb115afd',
'Sign21DiagonalDegree':'99434b7106531f142f6ac5e972d71a5d917c89410324c747a45b2870c98bf78f',
'Sign21AxisResidualDegree':'6c9d02b8fcc252a8379c8ba1c000e7f4caf650ec7ac1e53266dd6c72748e55cd',
'Sign21SquareCoeff':'1038f5f0f512d9bdff93208415e51b42073a8a550d28f4bc5d454496aea29b52',
'Sign21AxisCoeffLemmas':'cb777aca53ce80c2c15c7c39b68cd44cb821717c47d5305b45b4b719834a04f9',
'Sign21SeedCoefficient':'80037387c1b7729db3dba3399e37d1fc2d253a2e91b9d19c3713219a1d6d2012',
'Sign21DegreeLower':'21ac7528a9a48fdad4d9f9d5362907f51b7fbad6530e0bb1c027f0f0b663fedb'}
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
    expected = [('leading_row','leading_axis'), ('diagonal_totalDegree_le',), ('first_weighted_degree_le','other_weighted_degree_le','axisPoly_degree_le','axis_poly_degree_le'), ('leading_square_coeff',), ('square_coeff_zero','leading_axis_square_coeff','remaining_coeff'), ('leading_count','seed_axis_coeff'), ('diagonal_eval','direct_axis','expression_polynomial_degree_ge')][i]
    for th in expected: assert "Sign21LeadingRow."+th+"' depends on axioms:" in log
    assert log.count('warning:') == (9 if i == 2 else 1 if i == 5 else 0)
assert '14 ≤ (Sign21AbstractExpression.expression p).toPolynomial.totalDegree' in (packet/'src/DiophantineConsistency/Sign21DegreeLower.lean').read_text()
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign21-concrete-polynomial-bridge-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':89132,'outer_exit':0,
                  'children':7,'guards':guards,'warnings':10,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'Lean abstract sign21 polynomial totalDegree ≥14 for arbitrary integer ports; no external JSON/PDF binding'},sort_keys=True,indent=2))
