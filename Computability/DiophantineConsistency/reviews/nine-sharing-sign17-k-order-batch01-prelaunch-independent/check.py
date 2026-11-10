#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-order-batch01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d364f2e73e4e4b61e9cba33bc0ec2798efc51407131f381cad9b8f15fc66840e' and sha(p/'source-manifest.json')=='e2f5907ab484f440c22fdbc065fab3912bbd5ec9d0f4ceb1e7c0d9f86f019abd'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-k-weight-aggregate-batch01-check/source-manifest.json').read_text())['rows'];assert len(rows)==17 and rows[:16]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
e=rows[-1];assert e['module']=='DiophantineConsistency.Sign17KOrderBatch01' and e['imports']==['DiophantineConsistency.Sign17KWeightAggregateBatch01'];s=(p/'src/DiophantineConsistency/Sign17KOrderBatch01.lean').read_text()
for t in ('theorem indices_ne_zero (i : Fin 64) : indices i ≠ 0','theorem adjacent (i : Fin 63) : weights i.succ < weights i.castSucc','theorem actual_adjacent (i : Fin 63)','rw [all_weights, all_weights]','exact adjacent i'):assert t in s
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows'][32:96];assert len(w)==64 and all(x['index']!=0 for x in w) and all(x['weight']>y['weight'] for x,y in zip(w,w[1:]))
q=root/'reviews/nine-sharing-sign17-k-weight-aggregate-batch01-terminal-independent/check.py';assert sha(q)=='921818c7d83ff29fd06a828cb9e8a0568ec2081056af341333bd0d33a80d1279';subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':17,'scope':'within-block 64 nonzero indices and 63 adjacent actual weight inequalities; no cross-block or rank'},indent=2))
