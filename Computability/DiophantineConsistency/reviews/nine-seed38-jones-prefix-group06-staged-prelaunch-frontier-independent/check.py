#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-group06-staged-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'9bad1285dca775c666e1d67d8b9bbf0a70b6cddb084c335fa170f1d1eede1d02','provider_preflight.py':'ab939bfcf80281578a37c3fe472adeb3505dff876666529e6596c36509b806c6','source-manifest.json':'ef47306014b252a0273fd23fa7195688e53ae955b7606c5a413e17d15f3d8946'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroPrefixCarrySums','55adbc07f19d6493e3234f5755e4c19acfd641f9880b0e05cefbaeabcc56ee37',['d10_e_carry','d10_ell_carry','d10_lambda_carry']),('Norm38MacroPrefixCarryOthers','4f7ce529c5dc858ec7e0bed631228100a9561c1c8b2a6855a4907ed9b457006b',['d10_g_carry','d10_theta_carry','d10_B_carry','d10_b_carry'])];assert len(rows)==2
for row,(n,sha,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Norm38MacroPrefixQNCarry'];assert re.findall(r'^theorem (\w+)',s,re.M)==ts;assert re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 # Every Fin.last index used in a dN.values occurrence denotes a valid index of that prefix.
 for prefix,idx,casts in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(prefix)==int(idx)+1+casts.count('.castSucc')
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'seven uncompiled short-prefix carry identities; no Lean replay'},sort_keys=True,indent=2))
