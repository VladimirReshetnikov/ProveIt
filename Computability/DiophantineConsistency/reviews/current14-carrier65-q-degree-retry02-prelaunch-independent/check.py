#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-q-degree-retry02-check';old=root/'research/current14-carrier65-q-degree-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='2a84d7a441523bcc61ad4ef62a94f8d77d90a698a662e181f3b3fe471adbd431' and sha(p/'source-manifest.json')=='fe1bf27c70fdbb15482628be386b180fb414ff1516912cb07a9f2d5a3d66a2da'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65QDegree';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.WeightedExpressionDegree','Mathlib.Data.Fin.VecNotation'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert s==a.replace('Expr.evalRing_ofNat, Int.cast_ofNat]','Expr.evalRing_ofNat, Nat.cast_ofNat]') and s!=a
for f in ('current14-carrier65-q-degree-failure-independent','current14-carrier65-q-degree-retry-failure-independent','current14-carrier65-dag-value-congr-diagnostic-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and 'Q degree parent object absent' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'natural-cast generic Q degree retry, conditional input bounds retained'},indent=2))
