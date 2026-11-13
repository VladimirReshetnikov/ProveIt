#!/usr/bin/env python3
"""Read-only source and bounded cast controls; does not run Lean."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
PINS={
 'research/current2011-shear-rank-cast-generic-draft/RankCast.lean.src':'e66627d9c499e178cfb5005aaad5188fd05ba8d6586d7627be28e654b5f2b602',
 'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
 'Lean/DiophantineConsistency/ArithmeticPellFirstIndex.lean':'8cf79ed14f00f565accbfae0eb03ccacca597d06d12a509fecd6d3272e30f9ce',
 'research/current2011-shear-forward-index-binding-draft/ForwardIndex.lean.src':'fb39f3cb211700acd7e431da2f7a4e95a256a4a6f98087f8db0cb163beb9101a',
}
for name,h in PINS.items():
 if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=h: raise RuntimeError('source pin changed: '+name)
source=(ROOT/'research/current2011-shear-rank-cast-generic-draft/RankCast.lean.src').read_text()
for key in ('theorem cast_tsub_of_le','theorem gap_implies_F_le_q','theorem rank_cast','theorem c_cast','(hF : F ≤ q)'):
 if key not in source: raise RuntimeError('missing interface: '+key)
count=0
for q in range(1,8):
 for F in range(q+1):
  for alpha in range(4):
   for MC in range(4):
    for MF in range(4):
     for J in range(4):
      left=((max(q-1,0)*max(q-F,0)+alpha)*max(q*q-1,0)+(MC+q*MF)*J)
      right=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
      if left!=right: raise RuntimeError('bounded rank identity failed')
      count+=1
q,F,alpha,MC,MF,J=2,3,1,1,1,1
left=((max(q-1,0)*max(q-F,0)+alpha)*max(q*q-1,0)+(MC+q*MF)*J)
right=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
if left==right: raise RuntimeError('missing F<=q negative control')
print(json.dumps({'scope':'bounded controls and source pins only; draft unelaborated',
 'bounded_cases':count,'F_bound_negative_control':[left,right],'pinned_sources':len(PINS)},indent=2,sort_keys=True))
