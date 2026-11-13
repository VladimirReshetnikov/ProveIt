#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent08-staged-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'5a959e9792efe41514a70a930563cf9ea396e3b4aae400d78350a539c111eb4c','provider_preflight.py':'eab29e601f407dabb0dd48432ee4e607088ff308e77981592e8761ad749c062d','source-manifest.json':'700efce51b391d315b0d13b4e36579d220bb2652c437dbdd0d499928ce89b7ee'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroDependentBdCd','221a8bf6adbf8bab68c537caf7d2ade52c0602d03f12a090d4c8483edfeb74d7','Norm38MacroDependentV',['prefix_Bd','prefix_Cd']),('Norm38MacroDependentDmKc','836bbad65ae08ec2f70cc0c8af8eb600cccd81ccca7456083be4d88a39c03396','Norm38MacroDependentBdCd',['prefix_Dm','prefix_Kc']),('Norm38MacroDependentOutput','f2448afc57fa19d371082e6ecdc2b968fdb1af1792389abd1995845de9c87e27','Norm38MacroDependentDmKc',['prefix_T','prefix_output'])];assert len(rows)==3
for row,(n,sha,imp,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+imp];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
# Verify each immediate prefix references exactly the ordered source-DAG leaves.
named=(d/'research/nine-seed38-jones-named-prefix-draft/Norm38MacroPrefixes.lean').read_text()
for row,(n,sha,imp,ts) in zip(rows,expected):
 source=(p/'src/DiophantineConsistency'/f'{n}.lean').read_text()
 for theorem in ts:
  body=source.split('theorem '+theorem+' ',1)[1].split(':= by',1)[0]
  k=int(re.search(r'd(\d+)\.values a \(Fin.last',body).group(1)); src=re.search(r'^def d'+str(k)+r' : Dag .*$',named,re.M).group(0)
  assert list(map(int,re.findall(r'⟨(\d+), by decide⟩',body)))==list(map(int,re.findall(r'⟨(\d+), by decide⟩',src)))
  assert f'rw [d{k}, Norm38MacroCuts.snoc_last]' in source
  assert re.findall(r'\^ \(2 : Nat\)',body).__len__()==src.count('(.lit 2)')

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==3
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled Bd/Cd/Dm/Kc/T/output immediate-prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
