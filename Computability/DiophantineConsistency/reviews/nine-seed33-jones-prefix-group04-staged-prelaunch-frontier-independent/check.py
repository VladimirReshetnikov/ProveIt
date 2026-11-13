#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group04-staged-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='a5e12cf380e5980f867aacc6d65db7c5a482d632e558408c9d4b26c946b51eaf' and sha(P/'source-manifest.json')=='6b542a9ac99c274f8beaa28e50023ac12f6d6e83eff383cdf330976fe4dbb618'
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [x['module'] for x in m]==['DiophantineConsistency.Sign33MacroPrefixInputsA','DiophantineConsistency.Sign33MacroPrefixInputsB']
checks=[('InputsA',[('h',12,2,True),('s',13,3,True),('w',14,4,True)]),('InputsB',[('phi',15,5,False),('i',16,6,True),('j',17,7,True),('t',18,8,False)])]
for row,(suffix,thms) in zip(m,checks):
 n='Sign33MacroPrefix'+suffix;s=(P/'src/DiophantineConsistency'/f'{n}.lean').read_text();old=D/'research/nine-seed38-jones-prefix-group04-staged-check/src/DiophantineConsistency'/f'Norm38MacroPrefix{suffix}.lean'
 assert s==old.read_text().replace('Norm38','Sign33') and sha(P/'src/DiophantineConsistency'/f'{n}.lean')==row['source_sha256'] and row['imports']==['DiophantineConsistency.Sign33MacroPrefixGlarge']
 for name,node,index,add in thms:
  assert f'theorem prefix_{name} ' in s and f'd{node}.values a (Fin.last {node-1}) = a ⟨{index}, by decide⟩'+(' + ((1 : Int) : R)' if add else ' :=') in s and f'#print axioms prefix_{name}' in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':2,'short_prefix_identities':7,'scope':'input-node identities at d12 through d18 only'},sort_keys=True,indent=2))
