#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-weight-aggregate-batch14-15-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='117846d0290f335a99a8f1881d35c421802204c73ed2ddd10a3c28d66646b615' and sha(p/'source-manifest.json')=='bf275bee675805f96ecd1181a24015d2f613509e6eb8b3a726b639d34f05185f'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==17 and rows[:15]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows']
for e,b,start in zip(rows[15:],[14,15],[864,928]):
 name=f'Sign17KWeightAggregateBatch{b:02}';assert e['module']=='DiophantineConsistency.'+name and e['imports']==['DiophantineConsistency.Sign17ExactDegree'];s=(p/'src/DiophantineConsistency'/(name+'.lean')).read_text()
 length=64 if b==14 else 14;indices=re.search(r'def indices : Fin '+str(length)+r' → Fin 942 := !\[([^]]+)\]',s);weights=re.search(r'def weights : Fin '+str(length)+r' → ℕ := !\[([^]]+)\]',s);assert indices and weights
 assert [int(x) for x in indices[1].split(',')]==[x['index'] for x in w[start:start+length]] and [int(x) for x in weights[1].split(',')]==[x['weight'] for x in w[start:start+length]]
 assert ('theorem all_weights (i : Fin '+str(length)+') : selectorWeight (tile (indices i)) = weights i := by\n  fin_cases i <;> decide +kernel') in s and s.count('#print axioms ')==1 and 'set_option maxRecDepth 10000' in s and 'set_option maxHeartbeats 4000000' in s
for c,h in [('reviews/nine-sharing-sign17-k-ranking-witness-independent/check.py','9572d4eec346374dcc989fb070f4a488f06317a486efd36443818782e5f70150'),('reviews/nine-sharing-sign17-k-weight-aggregate-batch10-11-terminal-independent/check.py','73a41eb4762df42082bd10d38f86775ff8f78bb2e7e4bddc0297b51ac03083b0')]:
 q=root/c;assert sha(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
draft=root/'research/nine-sharing-sign17-k-weight-aggregate-batch14-15-draft';assert sha(draft/'generate14.py')=='051d2f554aa0bc94e36ca14099a53c26dd3119277c2a6f4b520e221c421e0008' and sha(draft/'generate15.py')=='e9ad12e5d7d4343bda214edcc01054c47212c695d9eff0082309f87b857a43e9';assert "['rows'][864:928]" in (draft/'generate14.py').read_text() and "['rows'][928:942]" in (draft/'generate15.py').read_text()
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':17,'weights':78,'scope':'78 actual Lean tile-weight proposals, no rank/K/file theorem'},indent=2))
