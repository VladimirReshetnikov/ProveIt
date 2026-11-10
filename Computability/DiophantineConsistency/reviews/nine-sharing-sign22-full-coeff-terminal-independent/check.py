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
packet = root/'research/nine-sharing-sign22-full-coeff-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign22-full-coeff-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session'] == 59967 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and 'failure' not in state
assert state['runner_sha256'] == digest(packet/'run.py') == '6b17282ee140a0aee818b7449338025799ea602055cd8c6a3fc34648f73e9185'
names = ['Sign22LeadingRows','Sign22DiagonalDegree','Sign22AxisResidualDegree','Sign22SquareCoeffs','Sign22AxisCoeffLemmas','Sign22SeedCoefficient','Sign22DegreeLower']
assert [r['module'] for r in state['rows']] == names
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
pins = {'Sign22CurrentExpressionDef':'e6af82e204a6e942979ad67fd20fcdf27138f5b17143eeb3b65553d20bb2cb14',
'Sign22LeadingRows':'5c68185d5dfdc8fd670b4526d99b540db422663b444e70ef656011ef16a01606',
'Sign22DiagonalDegree':'6d5252b5716fa82cb4ca345a77ed4a502931eb6347fdc309716c0fc4e3adacb6',
'Sign22AxisResidualDegree':'7e4458d782565ad23d3a695e207af3743e7cba4ecdf7bfbd2f02f5e5dd6e9994',
'Sign22SquareCoeffs':'637ff64aa97cfdddbfad11248ad95f4ccbae66509fe5dd4544e89bfd6899c2f1',
'Sign22AxisCoeffLemmas':'7398aae0d26fa2fa8eb25d32f0649f2b445275875804179c878444cd193f235f',
'Sign22SeedCoefficient':'08891bef44542749014f0ba8e324771af4281cbe27835f8ddb78e71a95b2ecb2',
'Sign22DegreeLower':'4ecdb9007664f9c3f07662c214bf487a47074640c12f94f280dff89faf8fbc4b'}
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
    expected = [('n0_row','dc2_row','n0_axis','dc2_axis'), ('diagonal_totalDegree_le',), ('first_weighted_degree_le','other_weighted_degree_le','axisPoly_degree_le','axis_poly_degree_le'), ('n0_square_coeff','dc2_square_coeff'), ('square_coeff_zero','n0_axis_square_coeff','dc2_axis_square_coeff','rows_distinct','remaining_coeff'), ('n0_count','dc2_count','seed_axis_coeff'), ('diagonal_eval','direct_axis','expression_polynomial_degree_ge')][i]
    for th in expected: assert "Sign22LeadingRows."+th+"' depends on axioms:" in log
    assert log.count('warning:') == (3 if i == 2 else 1 if i == 3 else 8 if i == 4 else 0)
assert '12 ≤ (Sign22AbstractExpression.expression p).toPolynomial.totalDegree' in (packet/'src/DiophantineConsistency/Sign22DegreeLower.lean').read_text()
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign22-concrete-polynomial-bridge-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':59967,'outer_exit':0,
                  'children':7,'guards':guards,'warnings':12,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'Lean abstract sign22 polynomial totalDegree ≥12 for arbitrary integer ports; no external JSON/PDF binding'},sort_keys=True,indent=2))
