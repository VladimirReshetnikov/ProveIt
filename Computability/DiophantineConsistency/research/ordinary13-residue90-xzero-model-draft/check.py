#!/usr/bin/env python3
"""Read-only finite algebra controls, not a Lean proof."""
from pathlib import Path
import hashlib,json,re,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue90-xzero-model-draft/Residue90XZeroArithmetic.lean.src': '144b5447d8fde7f6384e3fb5ae8311bc051bf563190d204db3dad4810df5914b', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'Lean/DiophantineConsistency/ModelRelationCombining.lean': '559df80321efb3854759ca9dcb20277533bba2568863ddf8e5059d81ac0cc5d6', 'Lean/DiophantineConsistency/ArithmeticSquareDivisibility.lean': 'f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660', 'Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean': '4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885', 'Lean/DiophantineConsistency/ModelDifferenceRing.lean': '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
s=(P/'Residue90XZeroArithmetic.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['theorem cancel_modulus','theorem modulus_dvd_scale','theorem xzero_impossible','ModelRelationCombining.sq_dvd_sq','Trace75IntegralTransport.natural_dvd_of_signed','linear_combination -U*hnorm+(d+a*c)*hw','linear_combination -4*hw']:
 assert x in s,x
rng=random.Random(139000);cases=0
for _ in range(600):
 H=rng.randrange(-10,11);U=rng.randrange(-10,11);d=rng.randrange(-10,11);a=rng.randrange(-10,11);c=rng.randrange(-10,11);w=rng.randrange(-10,11)
 norm=(d-a*c)*(d+a*c)-1-H*c*c; div=U*(d-a*c)-H*w
 target=U-H*(w*(d+a*c)-U*c*c)
 assert target==-U*norm+(d+a*c)*div
 cases+=1
for q in range(2,30):
 for Y in (q**3,q**3+1,q**3+q):
  H=3+4*Y;U=Y*q*q
  assert 3*q*q<H and H*q*q-4*U==3*q*q
print(json.dumps({'scope':'bounded source and integer ring controls, no Lean','pinned_files':len(pins),'ring_identity_cases':cases,'size_cases':84,'graph_extraction_and_provider_proofs_claimed':False,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
