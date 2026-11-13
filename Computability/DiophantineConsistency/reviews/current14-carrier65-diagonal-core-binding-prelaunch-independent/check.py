#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-core-binding-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='517c99b4862422570ede4a04d22a99eb4466249e21f6c021799b26400ed1268b' and sha(p/'source-manifest.json')=='dd5c4915f8bb5b230dcdc8fd34e60ce26b7e13d18b42ef3ae3db2139372d3536'
es=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Current14Carrier65DiagonalCore','Current14Carrier65DiagonalCoreBinding'];assert [e['module'].split('.')[-1] for e in es]==names
for e,n in zip(es,names):
 q=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',q.read_text(),re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',q.read_text())
assert (p/'src/DiophantineConsistency/Current14Carrier65DiagonalCore.lean').read_bytes()==(root/'research/current14-carrier65-diagonal-core-retry-check/src/DiophantineConsistency/Current14Carrier65DiagonalCore.lean').read_bytes()
s=(p/'src/DiophantineConsistency/Current14Carrier65DiagonalCoreBinding.lean').read_text()
for z in ('(Polynomial.X + Polynomial.X) * Current14Carrier65DiagonalBase.y (p 0) + Polynomial.X','(Polynomial.C (2 : ℤ) * Polynomial.X) * Current14Carrier65DiagonalBase.y (p 0) + Polynomial.X','(axisCore p).a = Current14Carrier65DiagonalCore.a (p 0)','(axisCore p).H = Current14Carrier65DiagonalCore.H (p 0)','(axisCore p).delta = Current14Carrier65DiagonalCore.delta (p 0)','(hp : p 0 ≠ 0)'):assert z in s
for name,val in [('c',5),('a',6),('H',6),('delta',12)]:assert f'(axisCore p).{name}.natDegree = {val}' in s and f'Current14Carrier65DiagonalCore.{name}_degree (p 0) hp' in s
for f in ('current14-carrier65-diagonal-binding-terminal-independent','current14-carrier65-diagonal-core-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed actual diagonal c/a/H/delta degrees under p0≠0; whole degree separate'},indent=2))
