#!/usr/bin/env python3
"""Bounded source and signed auxiliary controls; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue-aux-witness-model-draft/ResidueAuxWitness.lean.src': '1037e3a296285ae16c221d5beeebdde89050ee2ce74acf9e6335ba11a1935a1e', 'research/ordinary13-residue90-fy-model-draft/Residue90FyForce.lean.src': '1d4bd8b0f99b20a5796fe04f1ff0c4f5a825af65b1ba548a79aa0c0940a6e21a', 'research/ordinary13-residue90-fy-model-draft/check.py': 'dea3f83f6e516367e5ea6403be5f18639edae1de56acf7bf716667282731cf69', 'research/ordinary13-residue90-fy-model-draft/receipt.json': '06a116dee14ac52c48ef0e979cafa00502f7c875279c42b9decf13e3cac70e12', 'research/ordinary13-residue-exact-index-model-draft/ResidueExactIndexModel.lean.src': 'dc941fd8914795ac46f513f45979ef7c69c22a6d1be4dc332605f1ddb7a3a79a', 'research/ordinary13-residue-exact-index-model-draft/check.py': '9f9220d37a64a503d5c0a7804fcccbcaeebc729818f9c0cb0550227e145ba759', 'research/ordinary13-residue-exact-index-model-draft/receipt.json': 'db4dff7a02d19777927fd80f70093c36dc51b5f6d09409093d93918994857e81', 'research/ordinary14-natural81-combined-slim-overlay/source/AuxRootBridge.lean.src': '796819c48d53665e1ee9c90d8d1bfd0fbd00cd4ca5535fe4fad1a3462d74c8b7', 'Lean/DiophantineConsistency/Compact44/P72Root.lean': '066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091', 'Lean/DiophantineConsistency/ArithmeticPellHalfIndex.lean': '7703193660d8ae98408d1ec3a83f6f8811927252e739bb7af18dbafb833a8877', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet in ['ordinary13-residue90-fy-model-draft','ordinary13-residue-exact-index-model-draft']:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes(),packet
s=(P/'ResidueAuxWitness.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['ordinary_strong','ordinate_pair','old_aux_of_direct_graph','(hFq :','(hZ : (1 : DiffRing V)<ordinateRing','AuxRootModelDraft.square_gt_of_aux','AuxRootModelDraft.above_of_positive','P72Root.ι_magnitude_sq','∃ u : V, 0<u']:
 assert x in s,x
cases=0
for Q in range(2,101):
 for z in range(-200,201):
  if z*z<=1:continue
  n=Q*z*z-1
  if n%(Q-1):continue
  y=math.isqrt(n//(Q-1))
  if not y or y*y!=n//(Q-1):continue
  u=y-z;A=max(z,0);B=max(-z,0)
  assert u>0 and abs(A-B)**2==z*z and abs(A+u-B)**2==y*y
  assert Q*abs(A-B)**2+abs(A+u-B)**2==1+Q*abs(A+u-B)**2
  cases+=1
assert cases>0
for I in range(21):
 for delta in range(21):
  for f in range(21):assert I*I-delta*(f*f-1)==I*I+delta-delta*f*f
print(json.dumps({'scope':'bounded source and signed auxiliary controls, no Lean','pinned_files':len(pins),'finite_auxiliary_solutions':cases,'strict_ordinate_bound_explicit':True,'eta_zero_generalization_claimed':False,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
