#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-circuit-eval-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='c461ffaa17957570a6d798f2d252058d96cc9065f5a495c3d78231b74b4c2cc3' and sha(p/'source-manifest.json')=='6626925c85ed567343aa35da289cab3e16bd328d16a04c001263e861eb1c1499'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74CircuitEval';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74Circuit'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='5f491c36b2f331728fde561599bb98fbe9cc918ee872a925483c2a997e83f46d' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for f in ('nine-sharing-sign14-positive74-circuit-eval-source-independent','nine-sharing-sign14-positive74-circuit-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'one-pass symbolic and generic ring evaluator equality to positive74 expression; proposed rfl proofs untested; external file binding separate'},indent=2))
