#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-q-cancel-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='de402aa5b2af3b3fcf5cdd4d2fdd06543ee0784b70abf2588b988ea9e343e773' and sha(p/'source-manifest.json')=='7c449ea6e2c3c380e425267bf8c5b0b1956953f086ed1849fcad797b6afce73d'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65QCancel';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Carrier65'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(X + a * c + g * H) ^ 2 - (a ^ 2 + H) * c ^ 2','(X + g * H) ^ 2 + 2 * a * c * (X + g * H) - H * c ^ 2','d.Q = d.D ^ 2 - d.delta * d.c ^ 2','d.D = d.X + d.a * d.c + v 13 * d.H','d.delta = d.a ^ 2 + d.H','exact generic d.X d.a d.c d.H (v 13)'):assert z in s
c=(root/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert all(z in c for z in ('let D := X + a * c + gamma * H','let delta := a ^ 2 + H','let Q := D ^ 2 - delta * c ^ 2','let gamma := v 13'))
for f in ('current14-carrier65-dag-value-congr-diagnostic-terminal-independent','current14-carrier65-dag-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and '10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed Q algebraic cancellation only, not a degree bound'},indent=2))
