#!/usr/bin/env python3
"""Review corrected-axis actual Na degree candidate without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-axis-degree-lower-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='242b771c009a964bf82a450221541d57f052f5dfa838ab544bc6dc4a46b55368' and sha(m)=='07054107a1aa76f90096bc3e6181a54494717625555aa7ad5f22a097f7e909eb';rows=json.loads(m.read_text())['rows'];names=['Sign17UnivariateDegreeProbe','Sign17AxisDegreeBase','Sign17AxisDegreeRoot','Sign17AxisDegreeScale','Sign17AxisBindingBase','Sign17AxisBindingFactors','Sign17AxisBindingRoot','Sign17AxisNaDegree','Sign17AxisOtherDegree','Sign17AxisNoncancel','Sign17AxisSeedDegree','Sign17AxisDiagonalDegree','Sign17AxisDiagonalBinding','Sign17AxisDegreeLower'];assert [r['module'].split('.')[-1] for r in rows]==names;seen={'Sign17DegreeCompose','Equiv'}
for i,(row,name) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(root.parent.parent/row['source'])==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 for dep in row['imports']:assert dep.split('.')[-1] in seen
 seen.add(name)
 if i==4:assert 'def axis (i : Fin 18) : P := if i = 0 then 1 else if i = 17 then 0 else Polynomial.X' in s
 if i==7:
  assert row['imports']==['DiophantineConsistency.Sign17AxisBindingRoot'] and 'theorem row06_axis (p : Fin 4 → ℤ)' in s and 'theorem row06_axis_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0)' in s and '((row06 p).evalRing axis).natDegree = 48' in s and 'shared33_axis, axis13, axis17' in s
 if i==8:
  assert row['imports']==['DiophantineConsistency.Sign17AxisNaDegree'] and '[row00 p, row01 p, row02 p, row03 p, row04 p, row05 p, row07 p]' in s and 'theorem eval_degree_le' in s and 'theorem other_rows_axis_degree' in s and '(e.evalRing axis).natDegree ≤ 46' in s
 if i==9:
  assert row['imports']==['DiophantineConsistency.Sign17AxisOtherDegree'] and 'theorem other_sum_degree_le (p : Fin 4 → ℤ) : (otherSum p).natDegree ≤ 92' in s and 'theorem na_square_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0)' in s and 'theorem combined_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0)' in s and 'otherSum p).natDegree = 96' in s
 if i==10:
  assert row['imports']==['DiophantineConsistency.Sign17AxisNoncancel'] and 'theorem seed_axis (p : Fin 4 → ℤ)' in s and 'theorem seed_axis_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0)' in s and '((seed p).evalRing axis).natDegree = 96' in s
 if i==11:assert row['imports']==['DiophantineConsistency.Sign17AxisSeedDegree'] and 'if i = 16 then 0 else X 0' in s and 'theorem diagonal_totalDegree_le' in s and '(diagonal p).totalDegree ≤ p.totalDegree' in s
 if i==12:assert row['imports']==['DiophantineConsistency.Sign17AxisDiagonalDegree'] and 'if i = 16 then 0 else Polynomial.X' in s and 'theorem direct_axis' in s and '(SharingSeed17Degree96.seed p).evalRing axis' in s
 if i==13:assert row['imports']==['DiophantineConsistency.Sign17AxisDiagonalBinding'] and 'theorem expression_polynomial_degree_ge (p : Fin 4 → ℤ) (hz : p 0 ≠ 0)' in s and '96 ≤ (Sign17AbstractExpression.expression p).toPolynomial.totalDegree' in s
r=run.read_text();assert "if local=='Sign17DegreeCompose'" in r and "'Sign17AxisBindingRoot','Sign17AxisNaDegree','Sign17AxisOtherDegree','Sign17AxisNoncancel','Sign17AxisSeedDegree','Sign17AxisDiagonalDegree','Sign17AxisDiagonalBinding','Sign20DirectNoAliasNative'" in r and "elif mod=='Mathlib.Algebra.MvPolynomial.Equiv'" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
check=root/'reviews/nine-sharing-sign17-axis-seed-degree-terminal-independent/check.py';assert sha(check)=='292f7fdc5f0c7cb51fb33f45dc7631f8f86bee8130eee93fa94aaa7fe8b241a5';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':14,'runner_sha256':sha(run),'scope':'proposed actual Fin17 polynomial totalDegree ≥96 conditional on p0 nonzero; exact union/current specialization separate'},indent=2,sort_keys=True))
