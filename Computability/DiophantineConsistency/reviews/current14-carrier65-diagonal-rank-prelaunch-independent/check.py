#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-rank-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='38ef66f9de0a01df7245fd3fd9b27c9b58c2985e7af0d48b9b3c4d0eb734a5cd' and sha(p/'source-manifest.json')=='4fe2d51a93847c96a88a82ea11cbb2e3fdff9d2749e0bcc1cc825c6c850d213d'
es=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Current14Carrier65DiagonalDegree','Current14Carrier65DiagonalRank'];assert [e['module'].split('.')[-1] for e in es]==names
for e,n in zip(es,names):
 q=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',q.read_text(),re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',q.read_text())
assert (p/'src/DiophantineConsistency/Current14Carrier65DiagonalDegree.lean').read_bytes()==(root/'research/current14-carrier65-diagonal-degree-retry02-check/src/DiophantineConsistency/Current14Carrier65DiagonalDegree.lean').read_bytes()
s=(p/'src/DiophantineConsistency/Current14Carrier65DiagonalRank.lean').read_text()
for z in ('def axisVars (_ : Fin 14) : P := Polynomial.X','Carrier65.core (fun j => Polynomial.C (p j)) axisVars','(axisCore p).rank.natDegree ≤ 4','Current14Carrier65Diagonal.univariate_degree_le (rank p)','polynomial_bound (rank p)','rank_weight, Expr.evalRing_X','rw [rank_eval] at h'): assert z in s
for f in ('current14-carrier65-diagonal-degree-retry02-terminal-independent','current14-carrier65-other-fields-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed actual axis rank degree upper bound 4 for arbitrary integer ports; no whole-expression lower bound'},indent=2))
