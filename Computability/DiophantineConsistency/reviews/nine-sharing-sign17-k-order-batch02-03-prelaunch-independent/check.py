#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-order-batch02-03-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='6b6b3822b91fea94f6483256d61b69e9b5fb011202fc77f743538e931d258cda' and sha(p/'source-manifest.json')=='6d62b5f21725f10d1ce721d2db09562232ae59a68fa1067b23a58e4af9a9f3f1'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-k-weight-aggregate-batch02-03-check/source-manifest.json').read_text())['rows'];assert len(rows)==20 and rows[:17]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
ref=(root/'research/nine-sharing-sign17-k-order-batch01-check/src/DiophantineConsistency/Sign17KOrderBatch01.lean').read_text()
for i in (2,3):
 n=f'Sign17KOrderBatch{i:02}';s=(p/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert s==ref.replace('Batch01',f'Batch{i:02}');assert rows[15+i]['imports']==[f'DiophantineConsistency.Sign17KWeightAggregateBatch{i:02}']
b=(p/'src/DiophantineConsistency/Sign17KOrderBoundary02.lean').read_text();assert all(t in b for t in ('Sign17KWeightAggregateBatch03.weights 0 <','Sign17KWeightAggregateBatch02.weights 63','theorem actual_boundary','Sign17KWeightAggregateBatch03.all_weights, Sign17KWeightAggregateBatch02.all_weights'))
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows'];assert all(x['index']!=0 for x in w[96:224]) and all(x['weight']>y['weight'] for x,y in zip(w[96:223],w[97:224]))
for c,h in [('reviews/nine-sharing-sign17-k-weight-aggregate-batch02-03-terminal-independent/check.py','6a521f6145b170cb7319fe9a5827c1d228bd863911ea0e44fccf57a27b585f03'),('reviews/nine-sharing-sign17-k-order-batch01-terminal-independent/check.py','dd764d6ea25c36756dfce24ce377d5638a53b6d4f073e51128546c997a595ab3')]:q=root/c;assert sha(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':20,'scope':'within-block order rows96–223 and one boundary; no full candidate rank/K/file'},indent=2))
