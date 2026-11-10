#!/usr/bin/env python3
"""Review sign20 structured degree-upper candidate without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign20-degree-upper-check';draft=research/'nine-sharing-sign20-degree-upper-draft';prior=research/'nine-sharing-sign24-degree-structured-retry02-check'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='012c37aadc19f9760b1fadbfa5adf433ed7dc03c2bd074069b47975eda6d9b63'
rows=json.loads(m.read_text())['rows'];names=['Sign20SyntaxDegree','Sign20DegreeStructural','Sign20DegreeResiduals','Sign20DegreeCompose'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==['DiophantineConsistency.'+('Sign20CurrentExpressionDef' if i==0 else names[i-1])]
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
assert 'e.toPolynomial.totalDegree ≤ degree e' in texts[0]
assert 'degree (e.subst f) ≤ degree e' in texts[1] and 'removeInput_degree_le' in texts[1]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2 and '(e : Expr (Fin 21))' in texts[2]
branch=texts[2].split('rcases he with',1)[1].split('all_goals',1)[0];assert branch.count('rfl')==10
assert '(Sign20AbstractExpression.expression p).toPolynomial.totalDegree ≤ 20' in texts[3] and 'Sign20CurrentExpression.expression.toPolynomial.totalDegree ≤ 20' in texts[3]
assert all('maxHeartbeats' not in texts[i] for i in [0,1,3])
runner=packet/'run.py';assert sha(runner)=='5ade9659627823fb895ee93275caf0a29b9cf171f091fe7040cb6fdcd1133567';r=runner.read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "elif local=='Sign20CurrentExpressionDef':" in r and "elif local in ('Sign20SyntaxDegree','Sign20DegreeStructural','Sign20DegreeResiduals'):" in r
assert "need(not OUT.exists(),'output exists')" in r and "need(check_expression()==expression_data,'expression final drift')" in r
assert sha(packet/'expression-survey.py')==sha(draft/'expression-survey.py')=='6294f3ec92df189ad24dc8208375975de7141dbe52a99990c06f9d93ba1679d6'
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'remaining_branches':10,'scope':'proposed arbitrary-port sign20 polynomial degree ≤20; no Lean result or lower bound'},sort_keys=True,indent=2))
