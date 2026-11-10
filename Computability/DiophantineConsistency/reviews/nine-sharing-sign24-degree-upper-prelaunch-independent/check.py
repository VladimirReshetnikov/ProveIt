#!/usr/bin/env python3
"""Review proposed syntactic and polynomial total-degree upper bounds."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign24-degree-upper-check'
draft = research/'nine-sharing-sign24-degree-upper-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == '10676c339feb4f60c1c1bc260068e282d941125d52a58883d57c2bffc33640d2'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign24SyntaxDegree','Sign24DegreeUpper']
imports = [['DiophantineConsistency.Sign24CurrentExpressionDef'],['DiophantineConsistency.Sign24SyntaxDegree']]
texts = []
for row,name,expected in zip(rows,names,imports):
    assert row['module'] == 'DiophantineConsistency.'+name
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports'] == expected
    texts.append(src.read_text())
assert 'def degree {σ : Type*} : Expr σ → ℕ' in texts[0]
assert '| .constant _ => 0' in texts[0] and '| .var _ => 1' in texts[0]
assert '| .add a b | .sub a b => max (degree a) (degree b)' in texts[0]
assert '| .mul a b => degree a + degree b' in texts[0]
assert 'e.toPolynomial.totalDegree ≤ degree e' in texts[0]
assert 'theorem expression_syntax_degree (p : Fin 4 → ℤ)' in texts[1]
assert 'degree (Sign24AbstractExpression.expression p) = 8' in texts[1]
assert '(Sign24AbstractExpression.expression p).toPolynomial.totalDegree ≤ 8' in texts[1]
assert 'Sign24CurrentExpression.expression.toPolynomial.totalDegree ≤ 8' in texts[1]
assert not re.search(r'(?m)^\s*(axiom|opaque)\b', '\n'.join(texts))
runner = packet/'run.py'
assert digest(runner) == 'f7a888fbbabac8ecc1d56cddf7918de8ea91187d72511798cf16a71a090c2524'
assert "'-M3600'" in runner.read_text() and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner.read_text()
assert "elif local=='Sign24CurrentExpressionDef':" in runner.read_text() and "need(check_expression()==expression_data,'expression final drift')" in runner.read_text()
survey = packet/'expression-survey.py'
assert digest(survey) == '95df75084d293ce32734fb75d5a9b8798ff2bc16566b432aa91f585ccec275f7'
subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=120)
for review in ('nine-sharing-sign24-expression-eval-terminal-independent','nine-sharing-sign24-concrete-bridge-memory-retry-terminal-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),
                  'scope':'syntactic degree = 8, polynomial totalDegree ≤ 8, arbitrary integer ports; no lower bound or Lean result'},sort_keys=True,indent=2))
