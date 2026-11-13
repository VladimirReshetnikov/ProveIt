#!/usr/bin/env python3
"""Review sign17 axis base-factor candidate and two-stage guard without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-axis-root-binding-staged-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='61ada8d2dbb265d2c340a56c38dace9a3e33cf9ad33ce6657ddc15fd34562e2e' and sha(m)=='a0f740800d27c664e38d9c7e989cf1b0d53da100586bd134d02629b3cd1990e6';rows=json.loads(m.read_text())['rows'];names=['Sign17UnivariateDegreeProbe','Sign17AxisDegreeBase','Sign17AxisDegreeRoot','Sign17AxisDegreeScale','Sign17AxisBindingBase','Sign17AxisBindingFactors','Sign17AxisBindingRoot'];assert [r['module'].split('.')[-1] for r in rows]==names
for i,(row,name) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(root.parent.parent/row['source'])==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 if i==0:assert row['imports']==['DiophantineConsistency.Sign17DegreeCompose','Mathlib.Algebra.MvPolynomial.Equiv'] and sha(src)=='38621ad00c159eacb981acfb643bca3a0922c2b39dabfa2cc19cf389526cd916'
 elif i==1:assert row['imports']==['DiophantineConsistency.Sign17UnivariateDegreeProbe'] and 'theorem shift_degree : shift.natDegree = 1' in s and 'theorem shift_ne_zero : shift ≠ 0' in s and 'theorem affine_degree (z : ℤ) (hz : z ≠ 0)' in s
 elif i==2:assert row['imports']==['DiophantineConsistency.Sign17AxisDegreeBase'] and all('theorem '+n+' (z : ℤ) (hz : z ≠ 0)' in s for n in ('y_degree','e_degree','u_degree','dominant_degree')) and '(dominant z).natDegree = 11' in s
 elif i==3:assert row['imports']==['DiophantineConsistency.Sign17AxisDegreeRoot'] and all('theorem '+n+'_degree (z : ℤ) (hz : z ≠ 0) : ('+n+' z).natDegree = '+str(k) in s for n,k in (('low',2),('middle',7),('root',11),('scale',23)))
 else:assert row['imports']==['DiophantineConsistency.'+names[i-1]]
parts=[(p/'src/DiophantineConsistency'/(n+'.lean')).read_text() for n in names[4:]];alltext='\n'.join(parts);prior=(root/'research/nine-sharing-sign17-axis-root-binding-retry-draft/Sign17AxisRootBinding.lean').read_text();assert 'def axis (i : Fin 18) : P := if i = 0 then 1 else if i = 17 then 0 else Polynomial.X' in parts[0]
for n in ('07','26','24','29','33'):
 pat=r'theorem shared'+n+r'_axis \(p : Fin 4 → ℤ\) :\s*([^:]+):= by'
 assert re.findall(pat,prior)==re.findall(pat,alltext) and len(re.findall(pat,alltext))==1
assert 'all_goals ring' not in alltext and alltext.count('all_goals rfl')==4
failure=root/'reviews/nine-sharing-sign17-axis-root-binding-retry-failure-independent/check.py';assert sha(failure)=='394bc9c6c4b27b9246eac72c2dec82cfb1a9cfe49d4992caa950132779030cc5';subprocess.run([sys.executable,'-I','-S','-B',str(failure)],capture_output=True,check=True,timeout=120)
r=run.read_text();assert "if local=='Sign17DegreeCompose'" in r and "elif local in ('Sign17UnivariateDegreeProbe','Sign17AxisDegreeBase','Sign17AxisDegreeRoot','Sign17AxisDegreeScale','Sign17AxisBindingBase','Sign17AxisBindingFactors'" in r and "elif mod=='Mathlib.Algebra.MvPolynomial.Equiv'" in r and 'fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f' in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
check=root/'reviews/nine-sharing-sign17-univariate-degree-probe-retry02-terminal-independent/check.py';assert sha(check)=='0608299be3e408148c4f56ffe3c05b074798792377bfafffd783c1ca30e8ce53';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
axis=root/'reviews/nine-sharing-sign17-axis-degree-base-retry-terminal-independent/check.py';assert sha(axis)=='c373ed00f7a31cba52daec677ecf305bab35fcbe48261a0ff591e817e045ffef';subprocess.run([sys.executable,'-I','-S','-B',str(axis)],capture_output=True,check=True,timeout=120)
axis=root/'reviews/nine-sharing-sign17-axis-degree-root-terminal-independent/check.py';assert sha(axis)=='c1e57e40f4c7626f45f63b8c0917452df1927968f60e06965c1b5b034839bc21';subprocess.run([sys.executable,'-I','-S','-B',str(axis)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':7,'runner_sha256':sha(run),'scope':'split diagnostic for five corrected-axis identities; no Lean binding or lower bound yet'},indent=2,sort_keys=True))
