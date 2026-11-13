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
packet = root/'research/nine-sharing-sign20-degree-upper-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign20-degree-upper-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session'] == 77792 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and 'failure' not in state
assert state['runner_sha256'] == digest(packet/'run.py') == '5ade9659627823fb895ee93275caf0a29b9cf171f091fe7040cb6fdcd1133567'
names = ['Sign20SyntaxDegree','Sign20DegreeStructural','Sign20DegreeResiduals','Sign20DegreeCompose']
assert [r['module'] for r in state['rows']] == names
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
pins = {'Sign20CurrentExpressionDef':'325ed61a2f8d6f4af8516240f782f83d5ca83579c8184a7fad5dc066d02f96a3',
        'Sign20SyntaxDegree':'a6c7e7963fac3540887b730ab7e17c3bb91594f29f437e9c17cf6f65941d5c51',
        'Sign20DegreeStructural':'64acbda6298e3e1572ca50a2f9773f7d32cfb6e58334c85e1cec7bcdbb739b2d',
        'Sign20DegreeResiduals':'3f8da47211b8e1d795ed4642c71064826dda218a26dcbd73c62a052e6c101a44',
        'Sign20DegreeCompose':'392c5123a36030f5f44a7b013463bd33cdbc185dd6140a9e40fec6d212f5c615'}
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
    for th in expected: assert "Sign20SyntaxDegree."+th+"' depends on axioms:" in log
    assert log.count('warning:') == (4 if i == 2 else 0)
compose=(packet/'src/DiophantineConsistency/Sign20DegreeCompose.lean').read_text()
assert 'theorem expression_polynomial_degree_le (p : Fin 4 → ℤ)' in compose
assert '(Sign20AbstractExpression.expression p).toPolynomial.totalDegree ≤ 20' in compose
assert 'Sign20CurrentExpression.expression.toPolynomial.totalDegree ≤ 20' in compose
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':77792,'outer_exit':0,
                  'children':4,'guards':guards,'warnings':4,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'Lean sign20 polynomial totalDegree ≤ 20 for arbitrary ports and current ports; no exact degree or JSON/PDF binding'},sort_keys=True,indent=2))
