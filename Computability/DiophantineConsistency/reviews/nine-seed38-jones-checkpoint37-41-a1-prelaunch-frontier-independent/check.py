#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2]; P=D/'research/nine-seed38-jones-checkpoint37-41-a1-check'; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,h in {'run.py':'ac8130ae9329e12f6f896fce1032e5e42d0ed7fdbb4ed27a836a8712ca4d25cb','provider_preflight.py':'49ff8d2205ad9d5da05523e63e33fa5216b5c404c0532ef188f0d067edc88c33','source-manifest.json':'6cbf0d3e97dd10bf4f3b8b2cc91090bcfb4741bb64cab56e54da07d95531dc56'}.items():assert sha(P/name)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows']
want=[('Norm38MacroA1Value','124f298cb19240027583814ef65f4b721f6fc5378d5b36fa239836fd6cbae9c5',['Norm38MacroA0Path','Norm38MacroDependentA1'],['d37_A1_value']),('Norm38MacroA1Path','7660db034acc402ee4e6770ef41ca132c61544eb346010f4ee70cec91fb0b9a0',['Norm38MacroA1Value'],['path37_41','lookup37_41','d41_A1_value'])]
assert len(rows)==2
for r,(n,h,imp,ts) in zip(rows,want):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text()
 assert r['module']=='DiophantineConsistency.'+n and sha(p)==r['source_sha256']==h
 assert r['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+x for x in imp]
 assert re.findall(r'^theorem (\w+)',s,re.M)==ts==re.findall(r'^#print axioms (\w+)',s,re.M)
v=(P/'src/DiophantineConsistency/Norm38MacroA1Value.lean').read_text();q=(P/'src/DiophantineConsistency/Norm38MacroA1Path.lean').read_text()
def rhs(s,n):return ''.join(s.split('theorem '+n,1)[1].split(':= by',1)[0].split('=',1)[1].split())
s=rhs(v,'d37_A1_value')
for path,n in [('checkpoint35-41-i-check','d35_I_value'),('checkpoint32-41-f-check','d32_F_value'),('checkpoint30-41-d-check','d30_D_value')]:
 p=next((D/'research'/('nine-seed38-jones-'+path)/'src/DiophantineConsistency').glob('*Value.lean')); t=rhs(p.read_text(),n); assert t in s;s=s.replace(t,n.split('_')[1])
assert s=='(D)*(F)*(I)' and rhs(v,'d37_A1_value')==rhs(q,'d41_A1_value')
for t in ['(⟨29, by decide⟩ : Fin 36)','(⟨31, by decide⟩ : Fin 36)','(⟨34, by decide⟩ : Fin 36)','d36_D_carry','d36_F_carry','d36_I_carry','d30_D_value','d32_F_value','d35_I_value']:assert t in v
assert 'PrefixPath d37 d41' in q and '(i : Fin 37)' in q and q.count('PrefixPath.step')==4 and q.count('Dag.snoc')==4
nodes=(D/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text(); assert 'def d37 : Dag 37 := .snoc d36 (.mul (.mul (.ref ⟨29, by decide⟩) (.ref ⟨31, by decide⟩)) (.ref ⟨34, by decide⟩))' in nodes
for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',v+q):assert int(a)==int(b)+1+c.count('.castSucc')
base=Path('/tmp/nine-seed38-jones-checkpoint36-41-a0-check-20261106/lib/DiophantineConsistency')
for name,root,h in [('Norm38MacroA0Path','/tmp/nine-seed38-jones-checkpoint36-41-a0-check-20261106/lib/DiophantineConsistency','d8915cf6fe8fc9245466662f0d3c6389a0d4141d36af507fa8797d580ff5c043'),('Norm38MacroDependentA1','/tmp/nine-seed38-jones-dependent07-staged-check-20261106/lib/DiophantineConsistency','ceafb76103e30efb1f9c8a9cb4c57ec2c9d294c5a6c4c6f5b85fb6f1bcc58513')]:
 p=Path(root)/(name+'.olean'); q=base/(name+'.olean'); assert p.is_file() and q.resolve()==p.resolve() and sha(p)==sha(q)==h
assert sha(D/'research/nine-seed38-jones-checkpoint36-41-a0-check/attempt01/state.json')=='3223b4ced8c30d3f1de22fdd621720d0081fea7ee6ff05ee45921c8bd0ca9404'
assert not Path('/tmp/nine-seed38-jones-checkpoint37-41-a1-check-20261106').exists()
print(json.dumps({'status':'PASS_STATIC','scope':'A1 = D*F*I at d37 and carry to d41; Lean unrun; inherited point-in-time provenance limits'},indent=2,sort_keys=True))
