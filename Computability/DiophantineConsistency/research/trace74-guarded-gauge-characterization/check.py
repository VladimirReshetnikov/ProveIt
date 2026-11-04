#!/usr/bin/env python3
"""Finite diagnostic for the stated all-integer triangular characterization."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
root=Path(__file__).resolve().parents[2]
pins={'research/trace74-conditional-gauge-draft/Trace74ConditionalGauge.lean':'faf9a1be9a1dc890c904e598bcb665c6c7f43b7cb1d5dd3f9e29057cf646490f','research/trace74-guardfree-adjacent-draft/Trace74OffsetDiv.lean':'db50f4b5c7c4c9e0bef199a0bbe3681d6996d58162dcb6c5bdbeaa64133f1092','research/trace75-mask-coordinate-ring-probe/Trace74Mask.lean':'83ad7a62d50b10104099d8769c201c5514ed3afdabcf30ce1df8f4bb7774b7f0'}
def sha(x):return hashlib.sha256(x).hexdigest()
for path,h in pins.items():assert sha((root/path).read_bytes())==h
checks=0
for q in range(3,13):
 modulus=q**4;targets={}
 for F in range(1,q):
  for C in range(1,q-F):
   G=q*(q-F)-C
   assert 2*q-1<=G<=q*q-q-1 and G<modulus
   assert G not in targets
   targets[G]=(F,C)
 for g0 in range(modulus):
  inside=2*q-1<=g0<=q*q-q-1
  if inside:
   L=q*q-g0;f,c=divmod(L,q)
   admissible=1<=f and 1<=c and f+c<q
  else:admissible=False
  assert admissible==(g0 in targets)
  if admissible:assert (f,c)==targets[g0]
  for g in (g0,g0-modulus,g0+2*modulus):assert g%modulus==g0
  # Integer inverse of q²−1 mod q⁴, valid for every q, is −(1+q²).
  assert ((q*q-1)*(-(1+q*q)))%modulus==1
  checks+=1
for path,h in pins.items():assert sha((root/path).read_bytes())==h
print(json.dumps({'status':'PASS','source_pins':pins,'tested_q':'3..12','canonical_residues_tested':checks,'criterion':'2q−1≤g0≤q²−q−1 and f=L//q≥1, c=L%q≥1, f+c<q, L=q²−g0','scope':'Finite diagnostic for an independently reasoned integer characterization; no Lean theorem, arbitrary-q proof from enumeration, fixed payload, target zero, or gauge solvability claim.'},sort_keys=True,indent=2))
