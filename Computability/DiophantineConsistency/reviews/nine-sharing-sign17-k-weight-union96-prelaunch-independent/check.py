#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-weight-union96-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='5b74852fcb1e6be8191e4f155416e339d8723b1e9d5d5af8646e61285b18697c' and sha(p/'source-manifest.json')=='5782835b1e1c4d72f027dd6a426a77eb78e73eff4dbca73c2888a9f60c6de0b7'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==19 and rows[:15]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
for index,folder in [(15,'k-weight-aggregate-batch01'),(16,'k-weight-aggregate-probe'),(17,'k-weight-append')]:
 priorrows=json.loads((root/('research/nine-sharing-sign17-'+folder+'-check/source-manifest.json')).read_text())['rows'];assert rows[index]==priorrows[-1]
e=rows[-1];assert e['module']=='DiophantineConsistency.Sign17KWeightUnion96' and e['imports']==['DiophantineConsistency.Sign17KWeightAggregateProbe','DiophantineConsistency.Sign17KWeightAggregateBatch01','DiophantineConsistency.Sign17KWeightAppend'];s=(p/'src/DiophantineConsistency/Sign17KWeightUnion96.lean').read_text()
for t in ('def indices : Fin 96 → Fin 942 := Fin.append','def weights : Fin 96 → ℕ := Fin.append','theorem all_weights (i : Fin 96)','Sign17KWeightAppend.append_certificates','Sign17KWeightAggregateProbe.all_weights Sign17KWeightAggregateBatch01.all_weights i'):assert t in s
for c,h in [('reviews/nine-sharing-sign17-k-weight-aggregate-probe-terminal-independent/check.py','461e5f4c77a7d926a3dbac35f1bbf39b9c9b4e8162b19fe8c25e4fc4b9f32bd9'),('reviews/nine-sharing-sign17-k-weight-aggregate-batch01-terminal-independent/check.py','921818c7d83ff29fd06a828cb9e8a0568ec2081056af341333bd0d33a80d1279'),('reviews/nine-sharing-sign17-k-weight-append-terminal-independent/check.py','d429564176441c2bce0950903e0f026dc9363900ab2f9ca0e0ae90b41cb79ec5')]:q=root/c;assert sha(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':19,'scope':'proposed Fin96 union of audited weight vectors; rank/K/file separate'},indent=2))
