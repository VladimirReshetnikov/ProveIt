#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-coordinate-probe-retry02-check';old=root/'research/nine-sharing-sign14-positive74-coordinate-probe-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='9aab29a2e4de947ab5233f7ce44635c7f6aedc2a52e3a2cb976988dd9b4e1e5b' and sha(p/'source-manifest.json')=='cdbc7c01ca20fb1b2711e525600ebf0bfd05df2a5702796907a8288e9f49d889'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74CoordinateProbe';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74Expression'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
previous=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert previous.count('\n  ring\n')==1 and s==previous.replace('\n  ring\n','\n')
for f in ('nine-sharing-sign14-positive74-coordinate-probe-failure-independent','nine-sharing-sign14-positive74-coordinate-probe-retry01-failure-independent','nine-sharing-sign14-positive74-syntax-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'three generic ring node identities only; row/model/file proof separate'},indent=2))
