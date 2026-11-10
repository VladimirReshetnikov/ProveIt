#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-other-weights-retry02-check';old=root/'research/current14-carrier65-other-weights-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='376942cb1bdb5cde8744d87b0600a47ea0064871c73721142cea55ab60f4bebc' and sha(p/'source-manifest.json')=='b0d744e6424289535eb4606b6b5c35180cfc12dc55a45d13dcf16cc11ddef630'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65OtherWeights';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65QInputs'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert s==a.replace('  rw [hs, hv]\n','  rw [hs, hv]\n  rfl\n',1) and s!=a and max((0+23+23)+max(0+8+8,0+1+1),0+1+1)==62
for f in ('current14-carrier65-other-weights-failure-independent','current14-carrier65-other-weights-retry-failure-independent','current14-carrier65-q-inputs-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'closed arithmetic rfl retry; actual factor degree separate'},indent=2))
