#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-order-all-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='9af30abd986636472a6b76d4ca4786485ba232352f59fadf9686a4ed271e7c03' and sha(p/'source-manifest.json')=='00989ec839e9edac1a03867d3ff9a9c002620c0c2a91931b376a5230d09e81ae'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==17
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert rows[0]['module'].endswith('Sign17KOrderProbe') and rows[0]['imports']==['DiophantineConsistency.Sign17KWeightAggregateProbe']
probe=(p/'src/DiophantineConsistency/Sign17KOrderProbe.lean').read_text();assert all(x in probe for x in ('indices 0 = 0','i : Fin 31','indices i.succ ≠ 0','i : Fin 30','weights i.succ.succ < weights i.castSucc.succ','actual_nonstart_adjacent'))
ref=(p/'src/DiophantineConsistency/Sign17KOrderBatch01.lean').read_text()
for i in range(1,16):
 e=rows[i];n=f'Sign17KOrderBatch{i:02}';assert e['module']=='DiophantineConsistency.'+n and e['imports']==[f'DiophantineConsistency.Sign17KWeightAggregateBatch{i:02}'];s=(p/'src/DiophantineConsistency'/(n+'.lean')).read_text();expected=ref.replace('Batch01',f'Batch{i:02}')
 if i==15:expected=expected.replace('Fin 64','Fin 14').replace('Fin 63','Fin 13')
 assert s==expected
b=(p/'src/DiophantineConsistency/Sign17KOrderAllBoundaries.lean').read_text();assert rows[-1]['module']=='DiophantineConsistency.Sign17KOrderAllBoundaries' and len(rows[-1]['imports'])==16
for i in range(15):
 a='Sign17KWeightAggregateProbe' if i==0 else f'Sign17KWeightAggregateBatch{i:02}';z=f'Sign17KWeightAggregateBatch{i+1:02}';j=31 if i==0 else 63
 assert f'theorem boundary{i:02} : {z}.weights 0 < {a}.weights {j} := by decide +kernel' in b
 assert f'{z}.indices 0)) <\n      selectorWeight (tile ({a}.indices {j}))' in b and f'rw [{z}.all_weights, {a}.all_weights]\n  exact boundary{i:02}' in b
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows'];assert len(w)==942 and w[0]['index']==0 and all(x['index']!=0 for x in w[1:]) and all(w[i]['weight']>w[i+1]['weight'] for i in range(1,941))
for f in ('nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-ranking-witness-independent','nine-sharing-sign17-k-order-probe-terminal-independent','nine-sharing-sign17-k-order-batch01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':17,'blocks':16,'boundaries':15,'scope':'local Start/nonzero/adjacent certificates, conditional on Lean; global rank/K/file remain separate'},indent=2))
