#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-binding-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='186bb400abe66ea74beb3bdc1ddfca05464faf270441f6f9fc32ba28a560aad6' and sha(p/'source-manifest.json')=='d010b2086fbe94a6bf040dd4ade08ca0aa9f5599e435f9c0517327400beabc92'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DiagonalBinding';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DiagonalBase','DiophantineConsistency.Carrier65'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('def axisVars (_ : Fin 14) : P := Polynomial.X','Carrier65.core (fun j => Polynomial.C (p j)) axisVars','(axisCore p).q = Current14Carrier65DiagonalBase.q (p 0)','(axisCore p).X = Current14Carrier65DiagonalBase.x (p 0)','(axisCore p).Y = Current14Carrier65DiagonalBase.y (p 0)','(axisCore p).E = Current14Carrier65DiagonalBase.e (p 0)','(hp : p 0 ≠ 0)'):assert z in s
for z,val in [('q',1),('X',2),('Y',4),('E',6)]:assert f'(axisCore p).{z}.natDegree = {val}' in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-diagonal-base-retry-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and '10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed Carrier65 all-equal q/X/Y/E degrees under nonzero port0; whole diagonal separate'},indent=2))
