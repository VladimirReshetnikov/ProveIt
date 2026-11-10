#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-coordinate-arrangement-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='cb493ec8fb591f9bd9446ea45174a01b6f1d787d70125828d735e685dd6a6d72' and sha(p/'source-manifest.json')=='3fc1bad1d8baa4471d4b84307104753024d7008500d0d0ef4a155334e3776234'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectCoordinateArrangement';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectLeibnizParamNative'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('i.insertNth 0 (fun j => j.succ)','Fin.cons x (i.removeNth v) (focusIndex i j)) = Function.update v i x','Fin.insertNth_removeNth i x v','cases j using Fin.succAboveCases i'):assert z in s
for n0 in range(16):
 for i in range(n0+1):
  values=list(range(n0+1));rest=values[:i]+values[i+1:];focus=[0 if j==i else 1+(j if j<i else j-1) for j in range(n0+1)];res=[([100]+rest)[j] for j in focus];expected=values.copy();expected[i]=100;assert res==expected and sorted(focus)==list(range(n0+1))
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-leibniz-param-native-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'host finite-index focus and function update; no object-theory iteration'},indent=2))
