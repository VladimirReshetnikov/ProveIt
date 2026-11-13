#!/usr/bin/env python3
"""Review proposed full sign22 coefficient/lower bound stages without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign20-full-coeff-retry03-check';draft=research/'nine-sharing-sign20-full-coeff-retry03-draft';prior=research/'nine-sharing-sign20-leading-coeff-retry02-check'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='eead673b80c68ee61f4f95fa2ac9f09777523bb2d68c8707c1511efb473a215e'
rows=json.loads(m.read_text())['rows'];names=['Sign20LeadingRows','Sign20DiagonalDegree','Sign20AxisResidualDegree','Sign20SquareCoeffs','Sign20AxisCoeffLemmas','Sign20SeedCoefficient','Sign20DegreeLower'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
imports=[['Sign20CurrentExpressionDef'],['Sign20LeadingRows'],['Sign20LeadingRows'],['Sign20LeadingRows'],['Sign20AxisResidualDegree','Sign20SquareCoeffs'],['Sign20AxisCoeffLemmas'],['Sign20SeedCoefficient','Sign20DiagonalDegree']]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports[i]]
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
 if i<4:assert src.read_text()==(prior/'src/DiophantineConsistency'/(name+'.lean')).read_text()
prior_full=research/'nine-sharing-sign20-full-coeff-retry02-check/src/DiophantineConsistency'
for i,n in enumerate(names):
 old=(prior_full/(n+'.lean')).read_text()
 if i==5:
  a='simp [List.count_cons, SharingSeed20Degree20.remainingResiduals, n0, dc2, e, u, a, delta]'
  assert texts[i].count(a)==2 and texts[i].replace(a,'simp [SharingSeed20Degree20.remainingResiduals, n0, dc2, e, u, a, delta]')==old
 else:assert texts[i]==old
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-full-coeff-retry02-failure-independent/check.py')],check=True,capture_output=True,timeout=120)
assert '(h : e.weightedDegree weight ≤ 6)' in texts[4] and '(h : ∀ e ∈ rs, e ∈ SharingSeed20Degree20.remainingResiduals p)' in texts[4]
assert 'coeff index20 (axisSquares rs) = ((rs.count (n0 p) : ℤ) + (rs.count (dc2 p) : ℤ)) * (p 0)^4' in texts[4]
assert '(SharingSeed20Degree20.remainingResiduals p).count (n0 p) = 1' in texts[5]
assert '(SharingSeed20Degree20.remainingResiduals p).count (dc2 p) = 1' in texts[5]
assert 'coeff index20 ((SharingSeed20Degree20.seed p).evalRing axisPoly) = 2 * (p 0)^4' in texts[5]
assert 'diagonal (Sign20AbstractExpression.expression p).toPolynomial =' in texts[6] and '(SharingSeed20Degree20.seed p).evalRing axisPoly' in texts[6]
assert '(hp : p 0 ≠ 0)' in texts[6] and '20 ≤ (Sign20AbstractExpression.expression p).toPolynomial.totalDegree' in texts[6]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2 and texts[5].count('set_option maxHeartbeats 4000000 in')==2 and all('maxHeartbeats' not in texts[i] for i in [0,1,3,4,6])
runner=packet/'run.py';assert sha(runner)=='a592544ed5133152b0fb5513ec802a3c5585a74f1fedcbc18de6e08c935165a7';r=runner.read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "elif local=='Sign20CurrentExpressionDef':" in r and "elif local in ('Sign20LeadingRows','Sign20DiagonalDegree','Sign20AxisResidualDegree','Sign20SquareCoeffs','Sign20AxisCoeffLemmas','Sign20SeedCoefficient'):" in r
assert "need(not OUT.exists(),'output exists')" in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-leading-coeff-retry02-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'proposed conditional Lean expression polynomial degree ≥20 when p 0 ≠ 0; no Lean result or external binding'},sort_keys=True,indent=2))
