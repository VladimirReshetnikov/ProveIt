#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-b-power-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'91421b42fac65eebf910a862b93e697a4c8ec7748982cc99f149ceed73f81ccf','provider_preflight.py':'74ad27dafb598ca14f5dd9ff2252656c63ac88367dbfc41c3c134b1340100460','source-manifest.json':'8f9ae185cde6f210884616c4ad5fd5f1cb111c6309cda024ba4decb838fe6cc9','src/DiophantineConsistency/Norm38MacroPrefixBPower.lean':'85e269c6b2b31a8082f28a36dabb326cd50d82e5e4dd4b15b746b293918ca308'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Norm38MacroPrefixBPower.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='85e269c6b2b31a8082f28a36dabb326cd50d82e5e4dd4b15b746b293918ca308';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Norm38MacroPrefixCarryOthers'];assert re.findall(r'^theorem (\w+)',s,re.M)==['d10_B_eq_b_pow'];assert re.findall(r'^#print axioms (\w+)',s,re.M)==['d10_B_eq_b_pow']
found=re.findall(r'd10\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s);assert [(int(i),x.count('.castSucc')) for i,x in found]==[(1,8),(0,9)]
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled d10 B=b^5; no Lean replay'},sort_keys=True,indent=2))
