#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-rows-outer-retry01-check';old=root/'research/nine-sharing-sign14-positive74-rows-outer-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='57640062694f811a51ee65a32e0df9937fc006d0ad737c2eaf75048f9ff9de50' and sha(p/'source-manifest.json')=='0ff7fbb878b936890079ca6d45e35caa5c50ce3863f6ea8912ff8547cbf3407b'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74RowsOuter';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74SharedC'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
previous=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();expected=previous.replace('(row00 p).evalRing','(Sign14Positive74.row00 p).evalRing').replace('[row00,','[Sign14Positive74.row00,').replace('(row04 p).evalRing','(Sign14Positive74.row04 p).evalRing').replace('[row04,','[Sign14Positive74.row04,');assert s==expected
for f in ('nine-sharing-sign14-positive74-rows-outer-failure-independent','nine-sharing-sign14-positive74-shared-c-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'row00,row04,scale-square generic evaluations only; remaining rows/model/file separate'},indent=2))
