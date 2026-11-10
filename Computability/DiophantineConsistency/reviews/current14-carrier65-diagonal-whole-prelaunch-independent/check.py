#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-whole-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='573a315b645bc1abbbbb344a8f1cd239740c318c81620b650b50bb2dd9eef738' and sha(p/'source-manifest.json')=='685b90aaa7a5f64732f8e82e0ea568509ad88f826aec4ffef4282bd84bc138ce'
es=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Current14Carrier65DiagonalW','Current14Carrier65DiagonalQ','Current14Carrier65DiagonalWhole'];assert [e['module'].split('.')[-1] for e in es]==names
for e,n in zip(es,names):
 q=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',q.read_text(),re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',q.read_text())
for n,prior in [('Current14Carrier65DiagonalW','current14-carrier65-diagonal-w-retry02-check'),('Current14Carrier65DiagonalQ','current14-carrier65-diagonal-q-retry-check')]:
 assert (p/'src/DiophantineConsistency'/(n+'.lean')).read_bytes()==(root/'research'/prior/'src/DiophantineConsistency'/(n+'.lean')).read_bytes()
s=(p/'src/DiophantineConsistency/Current14Carrier65DiagonalWhole.lean').read_text()
for z in ('Carrier65.value (fun j => Polynomial.C (p j)) axisVars','(hp : p 0 ≠ 0)','(axisValue p).natDegree = 150','d.P.natDegree = 22','d.Q.natDegree = 18','d.U.natDegree = 62','d.W.natDegree = 2','d.Z.natDegree = 46','d.delta.natDegree = 12','(d.P * d.Q * d.U * d.W * d.Z - d.delta).natDegree = 150'):assert z in s
for f in ('current14-carrier65-diagonal-uz-terminal-independent','current14-carrier65-diagonal-w-retry02-terminal-independent','current14-carrier65-diagonal-q-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed actual all-equal Carrier65 axis degree 150 under p0 nonzero; multivariate transport and PDF separate'},indent=2))
