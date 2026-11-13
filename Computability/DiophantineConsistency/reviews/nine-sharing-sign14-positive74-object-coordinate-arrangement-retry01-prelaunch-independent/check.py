#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-coordinate-arrangement-retry01-check';old=root/'research/nine-sharing-sign14-positive74-object-coordinate-arrangement-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='77d667cf6dd61ce7a9d9183c05009e2fa6a3a157fff00f4b0b960e530d483699' and sha(p/'source-manifest.json')=='7c556f8582ab7bd7eddfd73db5ec7771502bc7c1e50346d07dfd48c0ca79e196'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectCoordinateArrangement';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectLeibnizParamNative'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert s==a.replace('Fin.cons x (i.removeNth v) (focusIndex i j)','(Fin.cons x (i.removeNth v) : Fin (n+1) → α) (focusIndex i j)') and s!=a
for f in ('nine-sharing-sign14-positive74-object-coordinate-arrangement-failure-independent','nine-sharing-sign14-positive74-object-leibniz-param-native-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'host finite-index focus/update retry; object-language transport separate'},indent=2))
