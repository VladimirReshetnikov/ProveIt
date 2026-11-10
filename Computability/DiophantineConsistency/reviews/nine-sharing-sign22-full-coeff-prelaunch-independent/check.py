#!/usr/bin/env python3
"""Review proposed full sign22 coefficient/lower bound stages without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign22-full-coeff-check';draft=research/'nine-sharing-sign22-full-coeff-draft';prior=research/'nine-sharing-sign22-leading-coeff-check'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='00f11a534f7fb437b8b941fb53441a3f6344dc1930a47a3e465affaae0aa5d00'
rows=json.loads(m.read_text())['rows'];names=['Sign22LeadingRows','Sign22DiagonalDegree','Sign22AxisResidualDegree','Sign22SquareCoeffs','Sign22AxisCoeffLemmas','Sign22SeedCoefficient','Sign22DegreeLower'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
imports=[['Sign22CurrentExpressionDef'],['Sign22LeadingRows'],['Sign22LeadingRows'],['Sign22LeadingRows'],['Sign22AxisResidualDegree','Sign22SquareCoeffs'],['Sign22AxisCoeffLemmas'],['Sign22SeedCoefficient','Sign22DiagonalDegree']]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports[i]]
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
 if i<4:assert src.read_text()==(prior/'src/DiophantineConsistency'/(name+'.lean')).read_text()
assert '(h : e.weightedDegree weight ≤ 4)' in texts[4] and '(h : ∀ e ∈ rs, e ∈ SharingSeed22Dodecic.remainingResiduals p)' in texts[4]
assert 'coeff index12 (axisSquares rs) = 16 * (rs.count n0 : ℤ) + 256 * (rs.count dc2 : ℤ)' in texts[4]
assert '(SharingSeed22Dodecic.remainingResiduals p).count n0 = 1' in texts[5]
assert '(SharingSeed22Dodecic.remainingResiduals p).count dc2 = 1' in texts[5]
assert 'coeff index12 ((SharingSeed22Dodecic.seed p).evalRing axisPoly) = 272' in texts[5]
assert 'diagonal (Sign22AbstractExpression.expression p).toPolynomial =' in texts[6] and '(SharingSeed22Dodecic.seed p).evalRing axisPoly' in texts[6]
assert '12 ≤ (Sign22AbstractExpression.expression p).toPolynomial.totalDegree' in texts[6]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2 and texts[5].count('set_option maxHeartbeats 4000000 in')==2 and all('maxHeartbeats' not in texts[i] for i in [0,1,3,4,6])
runner=packet/'run.py';assert sha(runner)=='6b17282ee140a0aee818b7449338025799ea602055cd8c6a3fc34648f73e9185';r=runner.read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "need(not OUT.exists(),'output exists')" in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign22-leading-coeff-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'proposed arbitrary-port Lean expression polynomial degree ≥12; no Lean result or external binding'},sort_keys=True,indent=2))
