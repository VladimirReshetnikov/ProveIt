#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-degree-direct-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d0a2d28ed1213f0d222c59ea75bca6e2232ebf3c81934ac206ba90ff08442b56' and sha(p/'source-manifest.json')=='bec2a0f9e8185986de8048485755d3b245aa572ff97ff203234bf6ff1d2c584e'
es=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Current14Carrier65DegreeUpper','Current14Carrier65DegreeDirect'];assert [e['module'].split('.')[-1] for e in es]==names
for e,n in zip(es,names):
 q=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',q.read_text(),re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',q.read_text())
assert (p/'src/DiophantineConsistency/Current14Carrier65DegreeUpper.lean').read_bytes()==(root/'research/current14-carrier65-degree-upper-check/src/DiophantineConsistency/Current14Carrier65DegreeUpper.lean').read_bytes()
s=(p/'src/DiophantineConsistency/Current14Carrier65DegreeDirect.lean').read_text()
for z in ('MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)','MvPolynomial.eval₂Hom MvPolynomial.C diagonalVars','Carrier65.value_map diagonalHom','diagonal (Carrier65.polynomial p)','Current14Carrier65DiagonalWhole.axisValue p','(hp : p 0 ≠ 0)','150 ≤ (Carrier65.polynomial p).totalDegree','Sign17UnivariateDegree.mapped_degree_le','diagonal_totalDegree_le (Carrier65.polynomial p)','Current14Carrier65DiagonalWhole.axis_degree p hp','(Carrier65.polynomial p).totalDegree = 150','Current14Carrier65DegreeUpper.polynomial_degree_le p'):assert z in s
for f in ('current14-carrier65-diagonal-whole-terminal-independent','current14-carrier65-degree-upper-terminal-independent','current14-carrier65-diagonal-degree-retry02-terminal-independent','current14-carrier65-degree-exact-failure-independent','current14-carrier65-degree-exact-retry-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
st=json.loads((root/'research/current14-carrier65-diagonal-degree-retry02-check/attempt01/state.json').read_text());rr=[x for x in st['rows'] if x['module']=='Current14Carrier65DiagonalDegree'];q=Path('/tmp/current14-carrier65-diagonal-rank-20261110/lib/DiophantineConsistency/Current14Carrier65DiagonalDegree.olean');assert st['status']=='PASS' and len(rr)==1 and sha(q)==rr[0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed Carrier65 polynomial totalDegree 150 under p0 nonzero only; current-port expression/PDF separate'},indent=2))
