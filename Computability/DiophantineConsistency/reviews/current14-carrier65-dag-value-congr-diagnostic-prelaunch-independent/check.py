#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-dag-value-congr-diagnostic-check';old=root/'research/current14-carrier65-dag-value-retry02-check';repo=root.parents[1];sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='b0146ec8e16127e0dd35e375b1f3b7e0f12a9850600193c837c846f578ff603e' and sha(p/'source-manifest.json')=='02e3c21325e5d5aa6a8ffaa616f77585a2021f0a19dba1f9797d9fcf61969328'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DAGValue';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DAGCore','DiophantineConsistency.Carrier65'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert s==a.replace('    one_mul, mul_one, mul_assoc]\n','    one_mul, mul_one, mul_assoc]\n  all_goals (first | rfl | congr 1)\n') and s!=a
for x in ('current14-carrier65-dag-failure-independent','current14-carrier65-dag-value-retry-failure-independent','current14-carrier65-dag-value-retry02-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/x/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and 'prior retry02 object absent' in r and 'successful children only' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'bounded one-step congruence diagnostic; prior failures and successful children of failed parent'},indent=2))
