#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-embedding-check'
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'45b76ca53c0206ab31183ddd7a33b3730ec4b22005d413eea3ba266f8119ae27','provider_preflight.py':'d5d5cdd0329010f925589c9307693f167f0cfdf8ef3a81e97ef6823788f07bad','source-manifest.json':'62fb80ef7282c12fcf5e99b30884f34d1f1ae2c50b654c8dd9ceb35abae85009','src/DiophantineConsistency/Norm38MacroPrefixEmbedding.lean':'0e44abd4d3cbc028dac5759b7091c3e861376f42f6327a4db11c1512ede71477'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Norm38MacroPrefixEmbedding.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='0e44abd4d3cbc028dac5759b7091c3e861376f42f6327a4db11c1512ede71477';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.Norm38MacroCuts'];assert re.findall(r'^theorem (\w+)',s,re.M)==['lookup','lookup_two'];assert re.findall(r'^#print axioms (\w+)',s,re.M)==['lookup','lookup_two']
for fragment in ['PrefixPath : {m n : Nat} → Dag m → Dag n → (Fin m → Fin n) → Prop','PrefixPath d d (fun i => i)','PrefixPath d (Dag.snoc e t) (fun i => (f i).castSucc)','e.values a (f i) = d.values a i','(Norm38MacroCuts.snoc_previous a _ t _).trans ih','(Dag.snoc (Dag.snoc d t) u).values a i.castSucc.castSucc = d.values a i']:assert fragment in s
c=(d/'research/nine-seed38-jones-compact-semantics-cut-check/src/DiophantineConsistency/Norm38MacroCuts.lean').read_text();assert '(Dag.snoc d t).values a i.castSucc = d.values a i' in c
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'generic prefix-path source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
