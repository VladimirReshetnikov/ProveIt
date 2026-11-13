#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-weight-union224-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='b153ff3a7c33051dc310943680d9f35f470acbe5adfa5fbc8f87acec95ebf9a4' and sha(p/'source-manifest.json')=='fdc211839a5ddeb41cb4e4508993db28d6a581c3586e8cae6794e19682ca332e'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==22 and rows[:15]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
union=json.loads((root/'research/nine-sharing-sign17-k-weight-union96-check/source-manifest.json').read_text())['rows'];batch=json.loads((root/'research/nine-sharing-sign17-k-weight-aggregate-batch02-03-check/source-manifest.json').read_text())['rows'];assert rows[:19]==union and rows[19:21]==batch[15:17]
e=rows[-1];assert e['module']=='DiophantineConsistency.Sign17KWeightUnion224' and e['imports']==['DiophantineConsistency.Sign17KWeightUnion96','DiophantineConsistency.Sign17KWeightAggregateBatch02','DiophantineConsistency.Sign17KWeightAggregateBatch03'];s=(p/'src/DiophantineConsistency/Sign17KWeightUnion224.lean').read_text()
for t in ('def indices160 : Fin 160 → Fin 942 := Fin.append','def weights160 : Fin 160 → ℕ := Fin.append','def indices : Fin 224 → Fin 942 := Fin.append indices160','def weights : Fin 224 → ℕ := Fin.append weights160','theorem all_weights160 (i : Fin 160)','theorem all_weights (i : Fin 224)','Sign17KWeightUnion96.all_weights Sign17KWeightAggregateBatch02.all_weights i','all_weights160 Sign17KWeightAggregateBatch03.all_weights i'):assert t in s
for c,h in [('reviews/nine-sharing-sign17-k-weight-union96-terminal-independent/check.py','c5e22ad098eab03b7c7accc164692df5e14610711b2afde791120c8151440aed'),('reviews/nine-sharing-sign17-k-weight-aggregate-batch02-03-terminal-independent/check.py','6a521f6145b170cb7319fe9a5827c1d228bd863911ea0e44fccf57a27b585f03')]:q=root/c;assert sha(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':22,'scope':'proposed Fin160/Fin224 union of audited weight vectors; rank/K/file separate'},indent=2))
