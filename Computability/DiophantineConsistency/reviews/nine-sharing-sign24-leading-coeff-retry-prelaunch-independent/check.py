#!/usr/bin/env python3
"""Review proposed leading-coefficient ingredients without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign24-leading-coeff-retry-check';draft=research/'nine-sharing-sign24-leading-coeff-retry-draft';prior=research/'nine-sharing-sign24-degree-lower-retry-check'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='6f3a7bf4556afdc0070c9d4b47383370ba44c33291ff3a8dbdd6930af38fc916'
rows=json.loads(m.read_text())['rows'];names=['Sign24LeadingN0','Sign24DiagonalDegree','Sign24AxisResidualDegree','Sign24N0SquareCoeff'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==(['DiophantineConsistency.Sign24CurrentExpressionDef'] if i==0 else ['DiophantineConsistency.Sign24LeadingN0'])
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
 if i<2:assert src.read_text()==(prior/'src/DiophantineConsistency'/(name+'.lean')).read_text()
assert 'if i = 16 ∨ i = 17 then 1 else 0' in texts[2]
assert '(he : e ∈ SharingSeed24Octic.remainingResiduals p) (hne : e ≠ n0)' in texts[2]
assert '(e.evalRing axisPoly).totalDegree ≤ 2' in texts[2]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2
assert 'MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 8)' in texts[3] and 'ℤ) = 1' in texts[3]
assert all('maxHeartbeats' not in texts[i] for i in [0,1,3])
old=research/'nine-sharing-sign24-leading-coeff-check'
for name in names[:3]: assert (old/'src/DiophantineConsistency'/(name+'.lean')).read_text()==(packet/'src/DiophantineConsistency'/(name+'.lean')).read_text()
oldcoeff=(old/'src/DiophantineConsistency/Sign24N0SquareCoeff.lean').read_text()
assert oldcoeff.split(':= by',1)[0]==texts[3].split(':= by',1)[0]
assert 'MvPolynomial.coeff_smul' in texts[3] and 'nsmul_eq_mul' in texts[3] and 'have hn :' in texts[3]
oldrunner=(old/'run.py').read_text()
assert oldrunner.replace('/tmp/nine-sharing-sign24-leading-coeff-20261109','/tmp/nine-sharing-sign24-leading-coeff-retry-20261109').replace('4678f2353db41272f00b878f0e7881b86c369f11450ea17ea56d099bf5bf68ab','6f3a7bf4556afdc0070c9d4b47383370ba44c33291ff3a8dbdd6930af38fc916').replace('Bounded sign24 leading coefficient ingredients','Bounded sign24 leading coefficient normalization retry').replace('PASS sign24 leading coefficient ingredients','PASS sign24 leading coefficient normalization retry')==(packet/'run.py').read_text()
runner=packet/'run.py';assert sha(runner)=='945d40a48bf45b1f3396afe5067e2fd2759af811c4121be3711e6626ab809f2e';r=runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "need(not OUT.exists(),'output exists')" in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign24-degree-lower-retry-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
survey=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(survey.stdout)['status']=='PASS'
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'leading coefficient ingredients only, no full lower bound or external binding'},sort_keys=True,indent=2))
