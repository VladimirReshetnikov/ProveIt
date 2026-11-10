#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-tile-sample-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='0e62fb5f10b3aaa3e348e9de72a6bd51fbe78b9cf51d7881c708068826e7c708' and sha(p/'source-manifest.json')=='d29a7cd487419fb002691cdc585554e892d00246211f4ec06019e59f81467504'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==19 and rows[:15]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows'];labels=['Start','Tail','Transition','Copy'];positions=[0,1,508,17];expected=[0,926,126,432]
for i,(label,pos,idx) in enumerate(zip(labels,positions,expected)):
 n='Sign17KTile'+label;e=rows[15+i];s=(p/'src/DiophantineConsistency'/(n+'.lean')).read_text();r=w[pos];assert r['index']==idx and e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.'+('Sign17ExactDegree' if i==0 else 'Sign17KTile'+labels[i-1])]
 assert f'theorem weight_{label.lower()} : selectorWeight (tile ({idx} : Fin 942)) = {r["weight"]} := by\n  decide +kernel' in s and 'set_option maxRecDepth 10000 in' in s and 'set_option maxHeartbeats 4000000 in' in s
for c,h in [('reviews/nine-sharing-sign17-k-ranking-witness-independent/check.py','9572d4eec346374dcc989fb070f4a488f06317a486efd36443818782e5f70150'),('reviews/nine-sharing-sign17-exact-degree-terminal-independent/check.py','ca5e8446ec5cbd623882721b116bd1c767bbe97afcd1689052cdccd97926a5d1')]:
 q=root/c;assert sha(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':19,'sample_indices':expected,'scope':'four actual Lean tile-weight sample proposals, no rank/K/file theorem'},indent=2))
