#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-q-actual-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='5101f02c8ef94179e18498147809cb94daf4f596b7726d65e0b252169da214b0' and sha(p/'source-manifest.json')=='13b81eb7a3ac8dad55e18558d0bc9ed955592e0812c6f9f08a6a339670f9f7bd'
es=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Current14Carrier65QCancel','Current14Carrier65QDegree','Current14Carrier65QActual'];assert [e['module'].split('.')[-1] for e in es]==names
for e,n in zip(es,names):
 q=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',q.read_text(),re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',q.read_text())
for n,folder in [('Current14Carrier65QCancel','current14-carrier65-q-cancel-check'),('Current14Carrier65QDegree','current14-carrier65-q-degree-retry02-check')]:assert (p/'src/DiophantineConsistency'/(n+'.lean')).read_bytes()==(root/'research'/folder/'src/DiophantineConsistency'/(n+'.lean')).read_bytes()
s=(p/'src/DiophantineConsistency/Current14Carrier65QActual.lean').read_text()
for z in ('![(core p).X, (core p).a, (core p).c, (core p).H, MvPolynomial.X 13]','core_X_degree p','core_a_degree p','core_c_degree p','core_H_degree p','MvPolynomial.X (13 : Fin 14)','Current14Carrier65QDegree.q_degree_le (values p) (values_degree p)','Current14Carrier65QCancel.current_core','(core p).Q.totalDegree ≤ 18'):assert z in s
old=(root/'research/current14-carrier65-q-actual-check/src/DiophantineConsistency/Current14Carrier65QActual.lean').read_text();assert s==old.replace('def core (p','noncomputable def core (p',1).replace('def values (p','noncomputable def values (p',1)
for f in ('current14-carrier65-q-actual-failure-independent','current14-carrier65-q-fields-terminal-independent','current14-carrier65-q-cancel-terminal-independent','current14-carrier65-q-degree-retry02-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and '768410b204858d98ae3e571beb8c1c0ff12268fa4706d42a7b0b1ecc28a2d643' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'noncomputable-only actual Q retry; prior failed final object and successful replays'},indent=2))
