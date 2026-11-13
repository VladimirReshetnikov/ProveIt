#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-degree-expression-current-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='6ab43ea0056c37150c6f0093dcbb85de9b368219e87f73e9764a922178351697' and sha(p/'source-manifest.json')=='01b3aef7d8c7680d43e2deae0e7cbb7cbd3378bc02c2828ee92e165db2b54ace'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DegreeExpressionCurrent';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DegreeExpression','DiophantineConsistency.Sign17ExactDegree'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports).toPolynomial.totalDegree = 150','Current14Carrier65DegreeExpression.expression_exact CurrentWindowCarry2011.ports','Sign17ExactDegree.current_port_nonzero'):assert z in s
for f in ('current14-carrier65-degree-expression-terminal-independent','nine-sharing-sign17-exact-degree-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
st=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/attempt01/state.json').read_text());rr=[x for x in st['rows'] if x['module']=='Sign17ExactDegree'];q=Path('/tmp/nine-sharing-sign17-k-weight-union942-20261110/lib/DiophantineConsistency/Sign17ExactDegree.olean');assert st['status']=='PASS' and len(rr)==1 and sha(q)==rr[0]['object_sha256'] and 'CurrentWindowCarry2011.ports 0 ≠ 0' in (root/'research/nine-sharing-sign17-exact-degree-check/src/DiophantineConsistency/Sign17ExactDegree.lean').read_text()
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed current-port in-Lean expression exact degree 150; TeX/PDF separate'},indent=2))
