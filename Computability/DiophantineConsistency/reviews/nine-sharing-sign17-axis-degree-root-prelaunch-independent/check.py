#!/usr/bin/env python3
"""Review sign17 axis base-factor candidate and two-stage guard without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-axis-degree-root-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='4c880a63527d3b77b9e94e4175c59b115c2b3f00180e788f3d49359410a2c0c6' and sha(m)=='ab49b933666383f216bccc96e945a13c5c93bf72cbdc0d61da1b074377da4b89';rows=json.loads(m.read_text())['rows'];names=['Sign17UnivariateDegreeProbe','Sign17AxisDegreeBase','Sign17AxisDegreeRoot'];assert [r['module'].split('.')[-1] for r in rows]==names
for i,(row,name) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(root.parent.parent/row['source'])==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 if i==0:assert row['imports']==['DiophantineConsistency.Sign17DegreeCompose','Mathlib.Algebra.MvPolynomial.Equiv'] and sha(src)=='38621ad00c159eacb981acfb643bca3a0922c2b39dabfa2cc19cf389526cd916'
 elif i==1:assert row['imports']==['DiophantineConsistency.Sign17UnivariateDegreeProbe'] and 'theorem shift_degree : shift.natDegree = 1' in s and 'theorem shift_ne_zero : shift ≠ 0' in s and 'theorem affine_degree (z : ℤ) (hz : z ≠ 0)' in s
 else:assert row['imports']==['DiophantineConsistency.Sign17AxisDegreeBase'] and all('theorem '+n+' (z : ℤ) (hz : z ≠ 0)' in s for n in ('y_degree','e_degree','u_degree','dominant_degree')) and '(dominant z).natDegree = 11' in s
r=run.read_text();assert "if local=='Sign17DegreeCompose'" in r and "elif local in ('Sign17UnivariateDegreeProbe','Sign17AxisDegreeBase'" in r and "elif mod=='Mathlib.Algebra.MvPolynomial.Equiv'" in r and 'fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f' in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
check=root/'reviews/nine-sharing-sign17-univariate-degree-probe-retry02-terminal-independent/check.py';assert sha(check)=='0608299be3e408148c4f56ffe3c05b074798792377bfafffd783c1ca30e8ce53';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
axis=root/'reviews/nine-sharing-sign17-axis-degree-base-retry-terminal-independent/check.py';assert sha(axis)=='c373ed00f7a31cba52daec677ecf305bab35fcbe48261a0ff591e817e045ffef';subprocess.run([sys.executable,'-I','-S','-B',str(axis)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':3,'runner_sha256':sha(run),'scope':'source-only degree-11 dominant root factor with nonzero-z assumption; staged-root binding and lower bound separate'},indent=2,sort_keys=True))
