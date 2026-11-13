#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-q-degree-retry-check';old=root/'research/current14-carrier65-q-degree-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='241530eba3e87ce328e0af59ec2bba5c60dfcae878be2624557e240a127d0c9d' and sha(p/'source-manifest.json')=='74d98b3688082831fcc419de21cd080d4d3862317d46007dc13301c1e6b1ecfa'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65QDegree';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.WeightedExpressionDegree','Mathlib.Data.Fin.VecNotation'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert s==a.replace('Expr.evalRing_pow, Expr.evalRing_var, Expr.evalRing_ofNat]','Expr.evalRing_pow, Expr.evalRing_var, Expr.evalRing_ofNat, Int.cast_ofNat]') and s!=a
for f in ('current14-carrier65-q-degree-failure-independent','current14-carrier65-dag-value-congr-diagnostic-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and 'Q degree parent object absent' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'cast-only generic Q degree retry, conditional input bounds retained'},indent=2))
