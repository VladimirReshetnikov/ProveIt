#!/usr/bin/env python3
"""Bounded ring/norm controls and source pins, not a Lean proof."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue-root-switch-extraction-draft/ResidueRootSwitchExtract.lean.src': '01d086c7d25b266f2385d9084f24ee8b9fc15e605eee97503a9b7329396e78f3', 'research/ordinary13-residue-root-switch-model-draft/ResidueRootSwitchArithmetic.lean.src': 'c9adec7548db6d9f1dd2e633e109ccb52b2ccc73490b31bd60bd7d7ae363de13', 'research/ordinary13-residue-root-switch-model-draft/check.py': '2259104f91ca92802a5caca028a573f50880526b6a51030f3d6cd2980e77b31d', 'research/ordinary13-residue-root-switch-model-draft/receipt.json': '46276b017358f08988b62178bc74514b69d3a6bd99ae623985b30158a8ff24b1', 'Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean': 'c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c', 'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean': '40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884', 'Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean': '4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885', 'Lean/DiophantineConsistency/ModelDifferenceRing.lean': '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
p=D/'research/ordinary13-residue-root-switch-model-draft'
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes()
s=(P/'ResidueRootSwitchExtract.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['theorem P_positive','theorem root_data','theorem positive_replacement','natural_magnitude_square','scaled_quotient','natural_dvd_of_signed','switch_from_zero']:
 assert x in s,x
rng=random.Random(138920);cases=0
for _ in range(500):
 b=rng.randrange(1,10);ell=rng.randrange(0,20);k=rng.randrange(2,15);P=-rng.randrange(0,15)
 z=b*(ell+k-k*P)-P;N=1+ell*(ell+k)
 assert z>=b*(ell+k)>0 and (ell+k)**2>N and z*z>b*b*N
 cases+=1
for _ in range(500):
 b,P,z,w,ell,k=[rng.randrange(-15,16) for _ in range(6)]
 hz=z-b*(ell+k-k*P)+P;hw=z-b*w
 assert hz-hw==P-b*(ell+k-k*P-w)
print(json.dumps({'scope':'bounded source and signed algebra controls, no Lean','pinned_files':len(pins),'P_nonpositive_cases':cases,'divisibility_identity_cases':500,'graph_preservation_and_parent_endpoint_open':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
