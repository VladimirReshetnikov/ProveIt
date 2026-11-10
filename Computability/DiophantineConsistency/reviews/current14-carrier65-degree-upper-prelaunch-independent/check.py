#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-degree-upper-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='01809f74481cdfde644e9ae79b0af57eb1455fddd1060dd89aea69877f480f92' and sha(p/'source-manifest.json')=='c5a1ca6834f9a5f5e8923ca5b582cab5f51638307d41335628d23cdee78101a3'
es=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Current14Carrier65QCancel','Current14Carrier65QDegree','Current14Carrier65QActual','Current14Carrier65DegreeUpper'];assert [e['module'].split('.')[-1] for e in es]==names
for e,n in zip(es,names):
 q=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',q.read_text(),re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',q.read_text())
for n in names[:3]:assert (p/'src/DiophantineConsistency'/(n+'.lean')).read_bytes()==(root/'research/current14-carrier65-q-actual-retry-check/src/DiophantineConsistency'/(n+'.lean')).read_bytes()
s=(p/'src/DiophantineConsistency/Current14Carrier65DegreeUpper.lean').read_text()
for z in ('(Carrier65.polynomial p).totalDegree ≤ 150','d.P.totalDegree ≤ 22','d.Q.totalDegree ≤ 18','d.U.totalDegree ≤ 62','d.W.totalDegree ≤ 2','d.Z.totalDegree ≤ 46','d.delta.totalDegree ≤ 12','(d.P * d.Q * d.U * d.W * d.Z - d.delta).totalDegree ≤ 150','MvPolynomial.totalDegree_sub','max_le hPQUWZ'):assert z in s
assert 22+18+62+2+46==150 and 12<=150
for f in ('current14-carrier65-other-fields-terminal-independent','current14-carrier65-q-actual-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed arbitrary-integer-port Carrier65 polynomial totalDegree ≤150; exact degree separate'},indent=2))
