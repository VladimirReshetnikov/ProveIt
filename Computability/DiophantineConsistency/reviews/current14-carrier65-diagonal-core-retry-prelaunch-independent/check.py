#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-core-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='e40bdee1b52e897ed6b58590b84660f320692c3691b5fefe780f4085a3627c9e' and sha(p/'source-manifest.json')=='8e5930507e121a515d9d08e55ba3f954808eeead31a2bb7f64d5290076c71006'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DiagonalCore';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DiagonalBase'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('Polynomial.C 2 * Polynomial.X','twice * Current14Carrier65DiagonalBase.y beta + Polynomial.X','Current14Carrier65DiagonalBase.e beta + Current14Carrier65DiagonalBase.y beta','Polynomial.C 4 * a beta + 3','a beta ^ 2 + H beta','(c beta).natDegree = 5','(a beta).natDegree = 6','(H beta).natDegree = 6','(delta beta).natDegree = 12','(hbeta : beta ≠ 0)'):assert z in s
assert max(1+4,1)==5 and max(6,4)==6 and max(6,0)==6 and max(2*6,6)==12
old=(root/'research/current14-carrier65-diagonal-core-check/src/DiophantineConsistency/Current14Carrier65DiagonalCore.lean').read_text();old=re.sub(r'(?<![\w.])(y_degree|e_degree|y|e)(?= beta)',r'Current14Carrier65DiagonalBase.\1',old);assert s==old
for f in ('current14-carrier65-diagonal-core-failure-independent','current14-carrier65-diagonal-base-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic diagonal c/a/H/delta exact degrees under beta nonzero; actual binding separate'},indent=2))
