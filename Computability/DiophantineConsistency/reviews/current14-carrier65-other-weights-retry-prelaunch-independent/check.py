#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-other-weights-retry-check';old=root/'research/current14-carrier65-other-weights-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='e6e52ae4a97c58904f0cc08c72055bb92644590e02b42325ea82986299a5eb76' and sha(p/'source-manifest.json')=='79f92722a0021d3923f4357cb6817030b5dddc1484ca1758bbf032223254c8ed'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65OtherWeights';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65QInputs'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
oldproof='theorem U_weight (p : Fin 4 → ℤ) : (U p).weightedDegree weight = 62 := by rfl';newproof='''theorem U_weight (p : Fin 4 → ℤ) : (U p).weightedDegree weight = 62 := by
  have hs := S_weight p
  have hv := V_weight p
  change max ((0 + (S p).weightedDegree weight + (S p).weightedDegree weight) +
    max (0 + (V p).weightedDegree weight + (V p).weightedDegree weight) (0 + 1 + 1))
    (0 + 1 + 1) = 62
  rw [hs, hv]''';assert s==a.replace(oldproof,newproof) and s!=a and max((0+23+23)+max(0+8+8,0+1+1),0+1+1)==62
for f in ('current14-carrier65-other-weights-failure-independent','current14-carrier65-q-inputs-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'staged U syntax-weight proof retry; actual factor degree separate'},indent=2))
