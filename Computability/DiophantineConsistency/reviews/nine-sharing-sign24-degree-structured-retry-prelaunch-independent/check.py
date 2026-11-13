#!/usr/bin/env python3
"""Review compositional sign24 degree-upper source and resource scope."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign24-degree-structured-retry-check'
draft = research/'nine-sharing-sign24-degree-structured-retry-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == 'c287002fe3fc8183807f0ea10bddde2b16f33f0060a43502f014e990bfe712b2'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign24SyntaxDegree','Sign24DegreeStructural','Sign24DegreeResiduals','Sign24DegreeCompose']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
imports = [['DiophantineConsistency.Sign24CurrentExpressionDef']]+[['DiophantineConsistency.'+n] for n in names[:-1]]
texts = []
for row,name,expected in zip(rows,names,imports):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports'] == expected
    assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text())
    texts.append(src.read_text())
assert 'e.toPolynomial.totalDegree ≤ degree e' in texts[0]
assert 'degree (e.subst f) ≤ degree e' in texts[1] and 'removeInput_degree_le' in texts[1]
assert 'degree (QuarticSyntax.sumExpressions (rs.map fun e => e * e)) ≤ 8' in texts[1]
assert texts[2].count('set_option maxHeartbeats 4000000 in') == 2
assert 'degree (SharingSeed24Octic.firstResidual p) ≤ 4' in texts[2]
assert '(he : e ∈ SharingSeed24Octic.remainingResiduals p) : degree e ≤ 4' in texts[2]
assert '(Sign24AbstractExpression.expression p).toPolynomial.totalDegree ≤ 8' in texts[3]
assert 'Sign24CurrentExpression.expression.toPolynomial.totalDegree ≤ 8' in texts[3]
assert all('maxHeartbeats' not in texts[i] for i in (0,1,3))
runner = packet/'run.py'
old = research/'nine-sharing-sign24-degree-structured-check'
old_runner = (old/'run.py').read_text()
new_runner = runner.read_text()
assert old_runner.replace('/tmp/nine-sharing-sign24-degree-structured-20261109','/tmp/nine-sharing-sign24-degree-structured-retry-20261109').replace('ece770bab14111a2e7621beb01b5bab73bb0910940aaf2c18a7da2f55699d3e8','c287002fe3fc8183807f0ea10bddde2b16f33f0060a43502f014e990bfe712b2').replace('Bounded sign24 structured degree attempt','Bounded sign24 structured degree residual retry').replace('PASS sign24 structured degree attempt','PASS sign24 structured degree residual retry') == new_runner
for i, name in enumerate(names):
    prior = (old/'src/DiophantineConsistency'/(name+'.lean')).read_text()
    if i == 2:
        prior = prior.replace('  simp [SharingSeed24Octic.firstResidual, degree]', '  decide').replace('  all_goals simp [degree]', '  all_goals decide')
    assert prior == texts[i]
assert 'native_decide' not in ''.join(texts)
assert "'-M3600'" in runner.read_text() and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner.read_text()
assert "elif local=='Sign24CurrentExpressionDef':" in runner.read_text() and "need(check_expression()==expression_data,'expression final drift')" in runner.read_text()
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign24-concrete-bridge-memory-retry-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'local_heartbeat_theorems':2,
                  'scope':'proposed arbitrary-port polynomial totalDegree upper bound; no Lean result or lower bound'},sort_keys=True,indent=2))
