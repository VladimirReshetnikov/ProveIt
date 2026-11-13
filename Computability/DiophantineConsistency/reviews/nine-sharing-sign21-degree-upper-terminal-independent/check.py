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
packet = root/'research/nine-sharing-sign21-degree-upper-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign21-degree-upper-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session'] == 56945 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and 'failure' not in state
assert state['runner_sha256'] == digest(packet/'run.py') == '401f651c85e4d8ff36e3ace5d5cb33959cbc72dc4aa3d03e4a34befc9896756a'
names = ['Sign21SyntaxDegree','Sign21DegreeStructural','Sign21DegreeResiduals','Sign21DegreeCompose']
assert [r['module'] for r in state['rows']] == names
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
pins = {'Sign21CurrentExpressionDef':'a8c661d9dd83991b57b0be84b013fee8c0a81b85f6a40981945c4693b9f8569e',
        'Sign21SyntaxDegree':'bd2029b44178c0132167e2399b1640468961f5e2a6bdc2a8d2aab85e772d096d',
        'Sign21DegreeStructural':'73db8708bd0e4f56c3e8236099ae49b6510dae9b557c92de6dc1e55a93e8b528',
        'Sign21DegreeResiduals':'c1391e4a50d9af9512cd3c163036bc116f58c262d65711478b80e91c1c867e7e',
        'Sign21DegreeCompose':'43a215883b539af6c6f8f5569b04b0dfa118cac59e1d91ff0696daf6f55088ef'}
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
    expected = [('polynomial_degree_le',), ('degree_subst_le','sum_squares_degree_le','removeInput_degree_le'), ('first_degree_le','remaining_degree_le'), ('seed_degree_le','expression_degree_le','expression_polynomial_degree_le','current_polynomial_degree_le')][i]
    for th in expected: assert "Sign21SyntaxDegree."+th+"' depends on axioms:" in log
    assert log.count('warning:') == (4 if i == 2 else 0)
compose=(packet/'src/DiophantineConsistency/Sign21DegreeCompose.lean').read_text()
assert 'theorem expression_polynomial_degree_le (p : Fin 4 → ℤ)' in compose
assert '(Sign21AbstractExpression.expression p).toPolynomial.totalDegree ≤ 14' in compose
assert 'Sign21CurrentExpression.expression.toPolynomial.totalDegree ≤ 14' in compose
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign21-concrete-polynomial-bridge-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':56945,'outer_exit':0,
                  'children':4,'guards':guards,'warnings':4,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'Lean sign21 polynomial totalDegree ≤ 14 for arbitrary ports and current ports; no exact degree or JSON/PDF binding'},sort_keys=True,indent=2))
