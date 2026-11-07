#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-current-source-iff-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'5967dfd049431626a954f0b726e4b6a143116f3ba468856a99a4fe5d7b7fead7','union-survey.py':'5b7fcc23a8ab41e3bba35df2cc5b3d560fddb4bb4b97fc633d755d618e4736b0','union.json':'9edf7fceb9593ed23e880d52d8990e5b188510c80b95909b10bf19772dfc3dce','source-manifest.json':'43bd04591d1cce216ef6183b0d6ad79ce97c52f0e121f970e0b087b0c2a7e1a0','src/DiophantineConsistency/Sign32CurrentSourceIff.lean':'94ae8b464dd8ed029f20fa4561a1a911c688419c6618f749194d930c9fd9f5bb'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.Sign32CurrentSeedIff','DiophantineConsistency.Sign33CurrentSeedIff']
s=(P/'src/DiophantineConsistency/Sign32CurrentSourceIff.lean').read_text();assert re.findall(r'^theorem (\w+)',s,re.M)==['exists_cons_iff','seed_exists_iff_source'] and len(re.findall(r'^#print axioms ',s,re.M))==2
for x in ['[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(∃ w : Fin n → V, P (Fin.cons (1 : V) w)) ↔','∃ v : Fin (n + 1) → V, v 0 = 1 ∧ P v','Fin.tail v','Fin.cons_self_tail v','∃ w : Fin 32 → V','Fin.cons (1 : V) w','∃ u : Fin 14 → V','ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u','Sign32CurrentSeedIff.exists_same_input (1 : V)','h33.symm.trans Sign33CurrentSeedIff.seed_exists_iff_source']:assert x in s
u=json.loads((P/'union.json').read_text());assert u['overlap_count']==1057 and len(u['extra'])==203
print(json.dumps({'status':'PASS_STATIC','scope':'32 natural witnesses at input 1 iff 14-variable current source; no Lean or external JSON binding'},indent=2,sort_keys=True))
