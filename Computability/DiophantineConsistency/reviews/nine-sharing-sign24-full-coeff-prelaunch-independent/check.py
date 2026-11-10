#!/usr/bin/env python3
"""Review proposed full sign24 coefficient/lower bound stages without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign24-full-coeff-check';draft=research/'nine-sharing-sign24-full-coeff-draft';prior=research/'nine-sharing-sign24-leading-coeff-retry-check'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='d3d2a0bee63074ef9ad1956a614dd335f8181fe204cf9743cdcddd8123ec62fd'
rows=json.loads(m.read_text())['rows'];names=['Sign24LeadingN0','Sign24DiagonalDegree','Sign24AxisResidualDegree','Sign24N0SquareCoeff','Sign24AxisCoeffLemmas','Sign24SeedCoefficient','Sign24DegreeLower'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
imports=[['Sign24CurrentExpressionDef'],['Sign24LeadingN0'],['Sign24LeadingN0'],['Sign24LeadingN0'],['Sign24AxisResidualDegree','Sign24N0SquareCoeff'],['Sign24AxisCoeffLemmas'],['Sign24SeedCoefficient','Sign24DiagonalDegree']]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports[i]]
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
 if i<4:assert src.read_text()==(prior/'src/DiophantineConsistency'/(name+'.lean')).read_text()
assert '(h : e.weightedDegree weight ≤ 2)' in texts[4] and '(h : ∀ e ∈ rs, e ∈ SharingSeed24Octic.remainingResiduals p)' in texts[4]
assert 'coeff index8 (axisSquares rs) = (rs.count n0 : ℤ)' in texts[4]
assert '(SharingSeed24Octic.remainingResiduals p).count n0 = 1' in texts[5]
assert 'coeff index8 ((SharingSeed24Octic.seed p).evalRing axisPoly) = 1' in texts[5]
assert 'diagonal (Sign24AbstractExpression.expression p).toPolynomial =' in texts[6] and '(SharingSeed24Octic.seed p).evalRing axisPoly' in texts[6]
assert '8 ≤ (Sign24AbstractExpression.expression p).toPolynomial.totalDegree' in texts[6]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2 and texts[5].count('set_option maxHeartbeats 4000000 in')==1 and all('maxHeartbeats' not in texts[i] for i in [0,1,3,4,6])
runner=packet/'run.py';assert sha(runner)=='274cf75bcc0766c76bbf4070be31ed701a6da8bcb86ae3386ef51f5f25dbe111';r=runner.read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "need(not OUT.exists(),'output exists')" in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign24-leading-coeff-retry-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'proposed arbitrary-port Lean expression polynomial degree ≥8; no Lean result or external binding'},sort_keys=True,indent=2))
