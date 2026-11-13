#!/usr/bin/env python3
"""Review proposed full sign21 coefficient/lower bound stages without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign21-full-coeff-check';draft=research/'nine-sharing-sign21-full-coeff-draft';prior=research/'nine-sharing-sign21-leading-coeff-check'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='8e9cd1f64abe9217a7ea99918cf17554011b88b11251f85956682cfe770bbce2'
rows=json.loads(m.read_text())['rows'];names=['Sign21LeadingRow','Sign21DiagonalDegree','Sign21AxisResidualDegree','Sign21SquareCoeff','Sign21AxisCoeffLemmas','Sign21SeedCoefficient','Sign21DegreeLower'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
imports=[['Sign21CurrentExpressionDef'],['Sign21LeadingRow'],['Sign21LeadingRow'],['Sign21LeadingRow'],['Sign21AxisResidualDegree','Sign21SquareCoeff'],['Sign21AxisCoeffLemmas'],['Sign21SeedCoefficient','Sign21DiagonalDegree']]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports[i]]
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
 if i<3:assert src.read_text()==(prior/'src/DiophantineConsistency'/(name+'.lean')).read_text()
assert '(h : e.weightedDegree weight ≤ 6)' in texts[4] and '(h : ∀ e ∈ rs, e ∈ SharingSeed21Degree14.remainingResiduals p)' in texts[4]
assert 'coeff index14 (axisSquares rs) = (rs.count leading : ℤ)' in texts[4]
assert '(SharingSeed21Degree14.remainingResiduals p).count leading = 1' in texts[5]
assert 'coeff index14 ((SharingSeed21Degree14.seed p).evalRing axisPoly) = 1' in texts[5]
assert 'diagonal (Sign21AbstractExpression.expression p).toPolynomial =' in texts[6] and '(SharingSeed21Degree14.seed p).evalRing axisPoly' in texts[6]
assert '14 ≤ (Sign21AbstractExpression.expression p).toPolynomial.totalDegree' in texts[6]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2 and texts[5].count('set_option maxHeartbeats 4000000 in')==1 and all('maxHeartbeats' not in texts[i] for i in [0,1,3,4,6])
runner=packet/'run.py';assert sha(runner)=='46dbe0051fdb6bda92f643ce122bc5985736c874fdb9d2c579004b0d8591beab';r=runner.read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "need(not OUT.exists(),'output exists')" in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign21-leading-coeff-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'proposed arbitrary-port Lean expression polynomial degree ≥14; no Lean result or external binding'},sort_keys=True,indent=2))
