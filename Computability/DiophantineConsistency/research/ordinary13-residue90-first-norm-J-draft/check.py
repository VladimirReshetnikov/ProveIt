#!/usr/bin/env python3
"""Bounded source and integer controls only; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue90-first-norm-J-draft/Residue90FirstNormJ.lean.src': 'ea7cdcfe04446f9d2fcf50849377e20959fda16df4cadafe7e5b07c1c5c815f6', 'research/ordinary13-residue90-first-norm-gap-draft/Residue90FirstNormGap.lean.src': '874a0b7254b5319e9a3f1891c700b3667854cd18a8ef1804474484fb70c93c1c', 'research/ordinary13-residue90-first-norm-gap-draft/check.py': 'ec70cec10d69e550e3ae163c5731e251c4d48482622bf3cb8757f37406231334', 'research/ordinary13-residue90-first-norm-gap-draft/receipt.json': '97f3829765c0d57d52cea6cdc6e62b117196f2f885eb6adc60107e6df3dc67db', 'research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src': '422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'Lean/DiophantineConsistency/ModelDifferenceRing.lean': '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
p=D/'research/ordinary13-residue90-first-norm-gap-draft'
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes()
s=(P/'Residue90FirstNormJ.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['theorem J_positive','theorem compact_gamma_of_X','first_ring_norm p v hz','(hX : 1≤v 6)','mul_self_eq_zero']:
 assert x in s,x
rng=random.Random(139001);cases=0
for _ in range(500):
 F=rng.randrange(1,15);alpha=rng.randrange(1,15);X=rng.randrange(0,15);K=rng.randrange(0,15);beta=rng.randrange(0,15)
 C=1-F-alpha;Bt=C*(X+K)-F;b=0;Z=-Bt
 assert C<=0 and Bt<0 and Z>0 and Z*Z>b*b
 cases+=1
print(json.dumps({'scope':'bounded source and J-zero integer controls; no Lean','pinned_files':len(pins),'integer_cases':cases,'represented_natural_ports_explicit':True,'X_positivity_remains_premise':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
