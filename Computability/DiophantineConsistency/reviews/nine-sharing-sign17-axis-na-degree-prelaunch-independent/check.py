#!/usr/bin/env python3
"""Review corrected-axis actual Na degree candidate without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-axis-na-degree-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='45756878021596d7342217eb71159ba0246969a9f5ba4358c10dddd985bc431f' and sha(m)=='866300265781ba5b43a6a08c8ab8a5a7828dbbd884b8b3889e9239325bcc031a';rows=json.loads(m.read_text())['rows'];names=['Sign17UnivariateDegreeProbe','Sign17AxisDegreeBase','Sign17AxisDegreeRoot','Sign17AxisDegreeScale','Sign17AxisBindingBase','Sign17AxisBindingFactors','Sign17AxisBindingRoot','Sign17AxisNaDegree'];assert [r['module'].split('.')[-1] for r in rows]==names;seen={'Sign17DegreeCompose','Equiv'}
for i,(row,name) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(root.parent.parent/row['source'])==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 for dep in row['imports']:assert dep.split('.')[-1] in seen
 seen.add(name)
 if i==4:assert 'def axis (i : Fin 18) : P := if i = 0 then 1 else if i = 17 then 0 else Polynomial.X' in s
 if i==7:
  assert row['imports']==['DiophantineConsistency.Sign17AxisBindingRoot'] and 'theorem row06_axis (p : Fin 4 → ℤ)' in s and 'theorem row06_axis_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0)' in s and '((row06 p).evalRing axis).natDegree = 48' in s and 'shared33_axis, axis13, axis17' in s
r=run.read_text();assert "if local=='Sign17DegreeCompose'" in r and "'Sign17AxisBindingRoot','Sign20DirectNoAliasNative'" in r and "elif mod=='Mathlib.Algebra.MvPolynomial.Equiv'" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
check=root/'reviews/nine-sharing-sign17-axis-root-binding-staged-retry-terminal-independent/check.py';assert sha(check)=='2c7f04546de5c9537d84e382ff9697f537ab7ce2f744588af7cbf3141b3c4ed3';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':8,'runner_sha256':sha(run),'scope':'proposed staged Na axis identity and degree 48 conditional on p0 nonzero; no sum lower or external binding'},indent=2,sort_keys=True))
