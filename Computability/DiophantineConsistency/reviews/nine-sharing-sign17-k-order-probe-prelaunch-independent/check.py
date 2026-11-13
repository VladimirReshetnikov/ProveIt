#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-order-probe-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='e41dfa7f7224fb13aea1b14c39a159b90206726af7ffe1f7577aac7847056d77' and sha(p/'source-manifest.json')=='31a8789f4f6b63039c5b29779dfe3eb66f397ce4a669105beac9a3f0c53c45f7'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-k-weight-aggregate-probe-check/source-manifest.json').read_text())['rows'];assert len(rows)==17 and rows[:16]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
e=rows[-1];assert e['module']=='DiophantineConsistency.Sign17KOrderProbe' and e['imports']==['DiophantineConsistency.Sign17KWeightAggregateProbe'];s=(p/'src/DiophantineConsistency/Sign17KOrderProbe.lean').read_text()
for t in ('theorem start_index : indices 0 = 0','theorem nonstart_indices_ne_zero (i : Fin 31) : indices i.succ ≠ 0','theorem nonstart_adjacent (i : Fin 30)','weights i.succ.succ < weights i.castSucc.succ','theorem actual_nonstart_adjacent (i : Fin 30)','rw [all_weights, all_weights]','exact nonstart_adjacent i'):assert t in s
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows'][:32];assert len(w)==32 and w[0]['index']==0 and all(x['index']!=0 for x in w[1:]) and all(x['weight']>y['weight'] for x,y in zip(w[1:31],w[2:32]))
q=root/'reviews/nine-sharing-sign17-k-weight-aggregate-probe-terminal-independent/check.py';assert sha(q)=='461e5f4c77a7d926a3dbac35f1bbf39b9c9b4e8162b19fe8c25e4fc4b9f32bd9';subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':17,'scope':'Start index0, non-Start 31 nonzero indices and 30 adjacent actual-weight inequalities; no cross-block or rank'},indent=2))
