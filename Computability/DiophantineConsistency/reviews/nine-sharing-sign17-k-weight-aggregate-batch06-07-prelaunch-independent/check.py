#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-weight-aggregate-batch06-07-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='50ef7f1ecfd777bc545b757d8d3bafbdbf479723fe93298d8d90c761344c3f15' and sha(p/'source-manifest.json')=='0a4650d552a47a0f5e96f88148cd92295442bf5c91214231fd37a726b5ce802f'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==17 and rows[:15]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows']
for e,b,start in zip(rows[15:],[6,7],[352,416]):
 name=f'Sign17KWeightAggregateBatch{b:02}';assert e['module']=='DiophantineConsistency.'+name and e['imports']==['DiophantineConsistency.Sign17ExactDegree'];s=(p/'src/DiophantineConsistency'/(name+'.lean')).read_text()
 indices=re.search(r'def indices : Fin 64 → Fin 942 := !\[([^]]+)\]',s);weights=re.search(r'def weights : Fin 64 → ℕ := !\[([^]]+)\]',s);assert indices and weights
 assert [int(x) for x in indices[1].split(',')]==[x['index'] for x in w[start:start+64]] and [int(x) for x in weights[1].split(',')]==[x['weight'] for x in w[start:start+64]]
 assert 'theorem all_weights (i : Fin 64) : selectorWeight (tile (indices i)) = weights i := by\n  fin_cases i <;> decide +kernel' in s and s.count('#print axioms ')==1 and 'set_option maxRecDepth 10000' in s and 'set_option maxHeartbeats 4000000' in s
for c,h in [('reviews/nine-sharing-sign17-k-ranking-witness-independent/check.py','9572d4eec346374dcc989fb070f4a488f06317a486efd36443818782e5f70150'),('reviews/nine-sharing-sign17-k-weight-aggregate-batch04-05-terminal-independent/check.py','43da50e7d4f5abbf3f1da04bdc36f646a979bb82b31b8b48dd0ebe69621ad35e')]:
 q=root/c;assert sha(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':17,'weights':128,'scope':'128 actual Lean tile-weight proposals, no rank/K/file theorem'},indent=2))
