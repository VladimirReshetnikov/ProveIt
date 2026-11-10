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
packet = root/'research/nine-sharing-sign24-degree-structured-retry02-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign24-degree-structured-retry02-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session_id'] == 82108 and outer['outer_exit_code'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and 'failure' not in state
assert state['runner_sha256'] == digest(packet/'run.py') == 'ed1f5e9e9d82e70c88c23efe8a8df106bbfe3da442bcbbc8ef40b3c7ebd83cc1'
names = ['Sign24SyntaxDegree','Sign24DegreeStructural','Sign24DegreeResiduals','Sign24DegreeCompose']
assert [r['module'] for r in state['rows']] == names
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
pins = {'Sign24CurrentExpressionDef':'c4461171b21c8317ec96470f066049d5d1457fcd934e71facadd2dd099e73f9f',
        'Sign24SyntaxDegree':'c587b45ef649a7a97c3bf1e96e79ac4c3f7616343093c5e92e67507494fe4bcd',
        'Sign24DegreeStructural':'d8455c48c6fe384b71cf85696cb9b7330c16e4fc9fd777858d93c1531d467800',
        'Sign24DegreeResiduals':'13970585bfb7575f2042d3da05b6ff2d8bf4175e822cceacd0cc05819b105495',
        'Sign24DegreeCompose':'8281e8be9dfe19dd6efa4faa05b4603b132feabbca3f33180325c8034e75f533'}
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
    for th in expected: assert "Sign24SyntaxDegree."+th+"' depends on axioms:" in log
    assert log.count('warning:') == (4 if i == 2 else 0)
compose=(packet/'src/DiophantineConsistency/Sign24DegreeCompose.lean').read_text()
assert 'theorem expression_polynomial_degree_le (p : Fin 4 → ℤ)' in compose
assert '(Sign24AbstractExpression.expression p).toPolynomial.totalDegree ≤ 8' in compose
assert 'Sign24CurrentExpression.expression.toPolynomial.totalDegree ≤ 8' in compose
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign24-concrete-bridge-memory-retry-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':82108,'outer_exit':0,
                  'children':4,'guards':guards,'warnings':4,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'Lean sign24 polynomial totalDegree ≤ 8 for arbitrary ports and current ports; no exact degree or JSON/PDF binding'},sort_keys=True,indent=2))
