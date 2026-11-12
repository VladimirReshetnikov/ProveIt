#!/usr/bin/env python3
"""Bounded signed-algebra controls, not Lean verification."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue-root-switch-model-draft/ResidueRootSwitchArithmetic.lean.src': 'c9adec7548db6d9f1dd2e633e109ccb52b2ccc73490b31bd60bd7d7ae363de13', 'research/ordinary13-residue-root-switch-model-audit/check.py': '2928aec8b11b2ede9bbd12537d6f143e2d91ac3cff147f2df0adc9873c2c0e47', 'research/ordinary13-residue-root-switch-model-audit/result.json': 'ffe60a4ae3c8b5228b0cde6e32f363fffdfb269670454c08b2f4ee49aa020f27', 'Lean/DiophantineConsistency/Compact44/P72Root.lean': '066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091', 'Lean/DiophantineConsistency/ModelDifferenceRing.lean': '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
p=D/'research/ordinary13-residue-root-switch-model-audit'
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'result.json').read_bytes()
s=(P/'ResidueRootSwitchArithmetic.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['negative_root_at_zero','switch_from_zero',"∃ r' : V",'hPt : P=b*t','linear_combination hs-hz+hpcast','linear_combination 2*hneg-hz']:
 assert x in s,x
rng=random.Random(138900);cases=0
for _ in range(600):
 b,P,t,ell,k,tau,z=[rng.randrange(-15,16) for _ in range(7)]
 hz=z-(b*(ell+k-k*P)-P);hs=z-b*tau;hp=P-b*t
 assert hs-hz+hp==b*(ell-k*(P-1)-t-tau)
 hn=z+b*tau;new=b*(ell+k+2*tau-k*P)-P
 assert 2*hn-hz==new+z
 cases+=1
print(json.dumps({'scope':'bounded source and signed ring controls; no Lean','pinned_files':len(pins),'signed_identity_cases':cases,'graph_quotient_and_other_residuals_obligations_explicit':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
