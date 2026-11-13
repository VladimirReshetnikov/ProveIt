#!/usr/bin/env python3
from pathlib import Path
from itertools import product
from math import isqrt
import hashlib,json
P=Path(__file__).resolve().parent; D=P.parents[1]
paths=[P/'FiveUnitFacts.lean',D/'Lean/DiophantineConsistency/ArithmeticNegativeNorms.lean',D/'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean',D/'research/ordinary14-negative-pell75/README.md',D/'research/ordinary14-positive-guard74/README.md']
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=paths[0].read_text()
for token in ('(hm : 2≤m)','ArithmeticNegativeNorms.consecutive_ne_negative','product5_positive hp','(hq : pairResidue q ≠ -1)','(hr : pairResidue r ≠ -1)','(ht : pairResidue t ≠ -1)','s.1=s.2+1'):
 assert token in s, token
assert 'import DiophantineConsistency.ModelArithmetic' not in s
negative=0
for m,k in product(range(2,102),range(201)):
 n=m*(m+1)*k*k-1
 if n>=0: assert isqrt(n)**2!=n
 negative+=1
units=0; guard_negative_controls=0
for q,r,s0,t in product(range(-2,3), repeat=4):
 for first in (-2,-1,0,1,2):
  if first*q*r*s0*t==1 and first!=-1 and q!=-1 and r!=-1 and t!=-1:
   assert (first,q,r,s0,t)==(1,1,1,1,1)
   units+=1
  if first*q*r*s0*t==1 and s0==-1: guard_negative_controls+=1
assert units>0 and guard_negative_controls>0
print(json.dumps({'scope':'finite controls and source-signature checks only; no Lean, provider or graph evaluation','files':{str(p.relative_to(D)):hashfile(p) for p in paths},'negative_pell_finite_cases':negative,'five_factor_positive_cases':units,'unrestricted_guard_negative_cases':guard_negative_controls},sort_keys=True,indent=2))
