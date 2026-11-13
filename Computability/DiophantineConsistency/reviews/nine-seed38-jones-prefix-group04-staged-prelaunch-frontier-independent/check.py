#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-group04-staged-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'a7aa641c2dd258134d1d6ac8f8f27e6f48a96dc692cc62024a257fec50f4ed91','provider_preflight.py':'022007831a83977a18481401e8d75e57c9b6d931f1592e7955dc0b6b56154d26','source-manifest.json':'a6d27222544cffc93752f16ab34cefc66e77968d8828425d02492d82da174510'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroPrefixInputsA','b9bbb4824dc8add66023e9ff695bc2541967548c137607a55d197d9104f58101',['prefix_h','prefix_s','prefix_w']),('Norm38MacroPrefixInputsB','262efba661c8dde99a92eeba9f3bb3fba79da9700554d3cda42525caefc341bc',['prefix_phi','prefix_i','prefix_j','prefix_t'])];assert len(rows)==2
for row,(n,sha,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Norm38MacroPrefixGlarge'];assert re.findall(r'^theorem (\w+)',s,re.M)==ts;assert re.findall(r'^#print axioms (\w+)',s,re.M)==ts
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'seven uncompiled short-prefix input values; no Lean replay'},sort_keys=True,indent=2))
