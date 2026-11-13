#!/usr/bin/env python3
"""Review sign17 axis base-factor candidate and two-stage guard without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-axis-degree-base-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='6102257bee280afcd292f052d1eafafc4beab79d3bbe0fd2ad00c783656759f4' and sha(m)=='599f45143ef0557faa48d94f6bd5358c3625f6a7437444bc43e5ca01401fdbaf';rows=json.loads(m.read_text())['rows'];names=['Sign17UnivariateDegreeProbe','Sign17AxisDegreeBase'];assert [r['module'].split('.')[-1] for r in rows]==names
for i,(row,name) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(root.parent.parent/row['source'])==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 if i==0:assert row['imports']==['DiophantineConsistency.Sign17DegreeCompose','Mathlib.Algebra.MvPolynomial.Equiv'] and sha(src)=='38621ad00c159eacb981acfb643bca3a0922c2b39dabfa2cc19cf389526cd916'
 else:assert row['imports']==['DiophantineConsistency.Sign17UnivariateDegreeProbe'] and 'theorem shift_degree : shift.natDegree = 1' in s and 'theorem shift_ne_zero : shift ≠ 0' in s and 'theorem affine_degree (z : ℤ) (hz : z ≠ 0)' in s
r=run.read_text();assert "if local=='Sign17DegreeCompose'" in r and "elif local in ('Sign17UnivariateDegreeProbe'" in r and "elif mod=='Mathlib.Algebra.MvPolynomial.Equiv'" in r and 'fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f' in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
check=root/'reviews/nine-sharing-sign17-univariate-degree-probe-retry02-terminal-independent/check.py';assert sha(check)=='0608299be3e408148c4f56ffe3c05b074798792377bfafffd783c1ca30e8ce53';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':2,'runner_sha256':sha(run),'scope':'source-only univariate shift and nonzero-z affine factors, no concrete lower degree or binding'},indent=2,sort_keys=True))
