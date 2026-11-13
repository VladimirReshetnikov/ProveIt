#!/usr/bin/env python3
"""Review sign20 structured degree-upper candidate without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign17-degree-upper-check';draft=research/'nine-sharing-sign17-degree-upper-draft';prior=research/'nine-sharing-sign24-degree-structured-retry02-check'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='cbb47d1de8bbe37cf971b9c31ffad2a2c7ee3a6777513033a0b6d4f27867251a'
rows=json.loads(m.read_text())['rows'];names=['Sign17SyntaxDegree','Sign17DegreeStructural','Sign17DegreeResiduals','Sign17DegreeCompose'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==['DiophantineConsistency.'+('Sign17CurrentExpressionDef' if i==0 else names[i-1])]
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
assert 'e.toPolynomial.totalDegree ≤ degree e' in texts[0]
assert 'degree (e.subst f) ≤ degree e' in texts[1] and 'removeInput_degree_le' in texts[1]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2 and '(e : Expr (Fin 18))' in texts[2]
branch=texts[2].split('rcases he with',1)[1].split('all_goals',1)[0];assert branch.count('rfl')==7
assert '(Sign17AbstractExpression.expression p).toPolynomial.totalDegree ≤ 96' in texts[3] and 'Sign17CurrentExpression.expression.toPolynomial.totalDegree ≤ 96' in texts[3]
assert all('maxHeartbeats' not in texts[i] for i in [0,1,3])
runner=packet/'run.py';assert sha(runner)=='49201fbf879e014190e651e99268aa6046a8799998d4c850118111c275de5b9e';r=runner.read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "if local=='Sign17CurrentExpressionDef':" in r and "elif local in ('Sign17SyntaxDegree','Sign17DegreeStructural','Sign17DegreeResiduals'):" in r
assert "need(not OUT.exists(),'output exists')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-expression-eval-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'remaining_branches':7,'scope':'proposed arbitrary-port sign17 polynomial degree ≤96; no Lean result or lower bound'},sort_keys=True,indent=2))
