#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-row02-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d394090c6567fc0ed59e276352a3e6d9c722e934f7266d02f0a2765fe869db8c' and sha(p/'source-manifest.json')=='66168628d1abffc1dd757613b30900d54a92f993b661e784f93ad9265a52cab0'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74Row02';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74CoordinateProbe'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='06ac9ba4610b67a62240331b6c27a838b86d614ac97779d047e5b7e5603f0e3d' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert '(row02 p).evalRing (fun i => v i + 1)' in s and "(Sign14Optimized86.row02' p).evalRing (Fin.cons 1 v)" in s
for i in (1,2,3,4,9):assert f'Fin.cases (1 : R) v ({i} : Fin 15) = v {i-1} := by rfl' in s
# Expanded row: old b=beta*(v0+1), a=K+(v8+1), x=a*(b-v1-(v2+1)); positive g26=b+1-(v1+1).
for beta in range(-2,3):
 for v0,v1,v2,v3,v8 in ((0,0,0,0,0),(1,2,3,4,5),(-2,1,-1,3,0)):
  b=beta*(v0+1);a=7+v8+1;x=a*(b-v1-(v2+1));old=x-v1-1-v3*b;u=[v0+1,v1+1,v2+1,v3+1,v8+1];new=(7+u[4])*(b+1-u[1]-u[2])-u[1]-(u[3]-1)*b;assert old==new
for f in ('nine-sharing-sign14-positive74-candidate-independent','nine-sharing-sign14-positive74-lean-draft-independent','nine-sharing-sign14-positive74-coordinate-probe-retry02-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'positive74/86 row02 generic ring equality only; other rows/model/file separate'},indent=2))
