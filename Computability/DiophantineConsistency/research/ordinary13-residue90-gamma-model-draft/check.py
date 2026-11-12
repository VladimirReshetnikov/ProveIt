#!/usr/bin/env python3
"""Bounded fact-level source and finite sanity check; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue90-gamma-model-draft/Residue90GammaModel.lean.src': '7a9f8a98e28bad9f94a8dccdab57d16753058f7eb55144fb5282f51a19314af7', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'research/ordinary13-natural-residue-forced90-degree56/check.py': '5f55c54a80c510b7862d5459c2ffddab585d18904d9b6d66c6a0fd0446195b5c', 'research/ordinary13-natural-residue-forced90-degree56/receipt.json': '81187a393eefdd7936c8bc9a1c4ad501c171b1e9ba01fd720ac8a06815d11efc', 'research/ordinary13-residue90-gamma-model-route-audit/check.py': '9bba5f5d088e59a8c5435e62af69f77e12ecc246f2c09dd23fac89b14459dba3', 'research/ordinary13-residue90-gamma-model-route-audit/result.json': 'a33d898f9b86dcaa69d170f82f1f5870fd01e1dcd526a43c08e165328ab6b49a', 'research/ordinary14-natural81-combined-slim-overlay/source/AuxRootBounds.lean.src': 'f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504', 'research/ordinary14-natural81-combined-slim-overlay/source/FirstMainLargeK.lean.src': '65d2de66fec31d7cc2d79687acc353638e864077c561af12829d93007d430e61', 'research/ordinary14-natural81-combined-slim-overlay/source/MainSquareGap.lean.src': '6639167627e5cf01814d1ae48f3975d42a72a6451863b31c9795b427ec6c5e68', 'research/ordinary14-natural80-gamma-narrow-draft/GammaZeroNarrow.lean': 'f64c3701ac0894998823fee6eaf7497549aa73b7448ae26b327983b6155642a7', 'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean': '374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('ordinary13-residue90-gamma-model-route-audit','check.py','result.json'),('ordinary13-natural-residue-forced90-degree56','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
s=(P/'Residue90GammaModel.lean.src').read_text()
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for t in ['theorem enlarged_rank_gap','(hq : 2≤q)','(hX : 1≤X)','(hY : q^3≤Y)','(R+X*Y*q)+1<k','FirstMainLargeKDraft.first_main_large_k','GammaZeroNarrowDraft.gamma_zero_impossible','(R+X*Y*q)','magnitude (P,N)']:
 assert t in s,t
assert 'q≤X' not in s.split('theorem enlarged_rank_gap',1)[1].split(':= by',1)[0]
g=json.loads((D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json').read_text());rows={r[0]:r for r in g['source']}
assert g['witnesses'][12]=='n_gamma' and rows['g54']==['g54','*','U','n_gamma'] and rows['g55']==['g55','*','E','q'] and rows['E']==['E','*','n_X','Y']
cases=0
for q in range(2,8):
 for x in range(1,7):
  for y in range(q**3,q**3+5):
   r=q**4-q**3-q-1
   assert r>=0
   for k in (8*x*y*y+4,8*x*y*y+13):
    assert r+x*y*q+1<k and x<1+y*k
    cases+=1
print(json.dumps({'scope':'bounded source and finite numerical sanity; no Lean','pinned_files':len(pins),'cases':cases,'extra_residue_term':'R+X*Y*q','q_le_X_not_assumed':True,'graph_extraction_and_provider_proof_claimed':False,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
