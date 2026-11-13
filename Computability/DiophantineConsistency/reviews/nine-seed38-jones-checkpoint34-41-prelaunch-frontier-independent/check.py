#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint34-41-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'8fd6c4ae946367a9c195508e3b92798151e85f1a67692cac096b3ead40dc4609','provider_preflight.py':'4486b459dd0434df2cb78bb0bc45b8c6a875e9ee95e8197d1f8bc4389872d597','source-manifest.json':'886a440cdf96ad7090068b0422d73fe28c4a20ed58b8f22b62d5305e990cb4a8','src/DiophantineConsistency/Norm38MacroCheckpoint34to41.lean':'aadc8c43e1b31996b95a7f9e9d1f7438cd4cd5b845680b38a8b0132e3396572b'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Norm38MacroCheckpoint34to41.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='aadc8c43e1b31996b95a7f9e9d1f7438cd4cd5b845680b38a8b0132e3396572b';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.Norm38MacroCheckpoint27to34','DiophantineConsistency.Norm38MacroLive18Group01','DiophantineConsistency.Norm38MacroPrefixQNCarry'];assert re.findall(r'^theorem (\w+)',s,re.M)==['path34_41','lookup34_41','d41_N_value']
path=s.split('theorem path34_41',1)[1].split('theorem lookup34_41',1)[0];assert 'PrefixPath d34 d41' in path and path.count('.castSucc')==7 and path.count('Dag.snoc')==7 and path.count('PrefixPath.step')==7
lookup=s.split('theorem lookup34_41',1)[1].split('theorem d41_N_value',1)[0];assert '(i : Fin 34)' in lookup and lookup.count('.castSucc')==7 and 'lookup path34_41 a i' in lookup
n=s.split('theorem d41_N_value',1)[1].split('#print',1)[0];first=n.split(':= by',1)[0];assert first.count('.castSucc')==37 and '((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)' in first and 'lookup18_41 a' in n and 'd18_N_carry a' in n and 'd10_N a' in n and 'Norm38MacroCuts.snoc_previous' in n
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(35,42):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'d34 to d41 path and concrete N source; no Lean replay'},indent=2,sort_keys=True))
