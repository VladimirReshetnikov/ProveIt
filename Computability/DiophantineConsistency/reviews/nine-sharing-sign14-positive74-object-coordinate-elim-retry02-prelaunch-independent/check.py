#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-coordinate-elim-retry02-check';old=root/'research/nine-sharing-sign14-positive74-object-coordinate-elim-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='27999e745ef938c7e6127ec0db2c3301ecf11d1ad4e1fb37973a9c4c6a85db39' and sha(p/'source-manifest.json')=='231c98a19dcfe479fdeb8eca818f98e3d693c36b9f5a42d7ad84223f58d3d05e'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectCoordinateElim';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text()
assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectGuardBind'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
a=a.replace('(x ⋏ ⋀ (y :: xs)) 🡒 x','(p ⋏ ⋀ (y :: xs)) 🡒 p').replace('listConjElim (y :: xs) p h','listConjElim (y :: xs) p (by simpa only [List.mem_cons] using h)');assert s==a
for z in ('theorem listConjElim :','p ∈ xs → extended nativeTheory ⊢ ((⋀ xs) 🡒 p)','Classical.choice ih','apply Classical.choice\n  apply listConjElim','nonzeroGuardOpen v 🡒 ∼eqAt (v i) zero','nonzeroGuardOpen v 🡒 eqAt (v i) (succ (pred (v i)))'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-coordinate-elim-failure-independent','nine-sharing-sign14-positive74-object-coordinate-elim-retry01-failure-independent','nine-sharing-sign14-positive74-object-guard-bind-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'Prop-level conjunction membership with host proof selection; pointwise object-theory conclusions unchanged'},indent=2))
