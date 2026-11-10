#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-circuit-output-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='ace15c886b5c1c0ece98c5d94a868a0f75d8af825931beba44d04a133fa45766' and sha(p/'source-manifest.json')=='f793fb37c6585395a55903c0444c470c19122891f1b49ec35237c6009344b602'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74CircuitOutput';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74CircuitTransitions08'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='a10580f3efc256819c276d97e9da5905c1b0214f592b66eaaccd2d8b134a8914' and re.findall(r'^import (\S+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for f in ('nine-sharing-sign14-positive74-circuit-output-source-independent','nine-sharing-sign14-positive74-circuit-transitions-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r and "for row in base['rows']:" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed state74 register73 symbolic and generic ring equality to positive74 expression; full graph/file binding separate'},indent=2))
