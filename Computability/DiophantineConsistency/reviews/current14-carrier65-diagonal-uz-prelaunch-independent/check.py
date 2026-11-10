#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-uz-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='0af6df96f832752134173362779ea21ce8d0166d24a51a6cb86c7f1c8e306a1d' and sha(p/'source-manifest.json')=='ce19ea3bae67ca3377f6e57aaa1f1cf5ce62e2de266e1991764557d7aaa955db'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DiagonalUZ';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DiagonalP'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(axisCore p).V.natDegree = 8','(axisCore p).S.natDegree = 23','(axisCore p).U.natDegree = 62','(axisCore p).Z.natDegree = 46','(hp : p 0 ≠ 0)','d.rank.natDegree ≤ 4','d.c.natDegree = 5','d.delta.natDegree = 12','d.S ^ 2 * (d.V ^ 2 - (Polynomial.X : P) ^ 2) + (Polynomial.X : P) ^ 2','d.delta * (Polynomial.X : P) ^ 2 - d.S ^ 2'):assert z in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-diagonal-p-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed actual V/S/U/Z axis degrees 8/23/62/46 under p0 nonzero; whole degree separate'},indent=2))
